import SpecDerive.RunningSum.Spec

namespace RunningSum

theorem cum_of_consistent {e : Entry} {t : List Entry} (h : Consistent (e :: t)) :
    e.cum = e.x + reference t := by
  simp only [Consistent, reference] at h
  exact h.1

theorem plan_correct : PlanCorrect := by
  unfold PlanCorrect
  intro s h
  cases s with
  | nil => rfl
  | cons e t => simp only [plan, reference]; exact cum_of_consistent h

theorem inRange_iff (e : Entry) : inRange e = true ↔ InRange e := by
  simp only [inRange, InRange, Bool.and_eq_true, decide_eq_true_eq]

theorem checkFrom_iff (e : Entry) (t : List Entry) :
    checkFrom e t = true ↔ Consistent (e :: t) ∧ ∀ y ∈ t, InRange y := by
  induction t generalizing e with
  | nil =>
    simp only [checkFrom, beq_iff_eq, Consistent, reference, Int.add_zero, and_true,
      List.not_mem_nil, false_implies, implies_true]
  | cons e' t ih =>
    simp only [checkFrom, Bool.and_eq_true, beq_iff_eq, inRange_iff, ih, Consistent, reference,
      List.forall_mem_cons]
    constructor
    · rintro ⟨hr, hc, ⟨hc', hct⟩, hall⟩
      exact ⟨⟨by rw [hc, hc'], hc', hct⟩, hr, hall⟩
    · rintro ⟨⟨hc, hc', hct⟩, hr, hall⟩
      exact ⟨hr, by rw [hc, hc'], ⟨hc', hct⟩, hall⟩

theorem check_sound : CheckSound := by
  unfold CheckSound Invariant ValuesBounded
  intro s h
  cases s with
  | nil => simp [Consistent]
  | cons e t =>
    simp only [checkInvariant, Bool.and_eq_true, inRange_iff, checkFrom_iff] at h
    exact ⟨h.2.1, List.forall_mem_cons.mpr ⟨h.1, h.2.2⟩⟩

theorem check_complete : CheckComplete := by
  unfold CheckComplete Invariant ValuesBounded
  intro s ⟨hc, hb⟩
  cases s with
  | nil => rfl
  | cons e t =>
    have hb := List.forall_mem_cons.mp hb
    simp only [checkInvariant, Bool.and_eq_true, inRange_iff, checkFrom_iff]
    exact ⟨hb.1, hc, hb.2⟩

/-! ## Integer bounds -/

theorem bounded_tail : BoundedTail := by
  unfold BoundedTail Bounded
  intro e t ⟨hl, hm⟩
  simp only [List.length_cons] at hl
  exact ⟨by omega, fun x hx => hm x (List.mem_cons_of_mem _ hx)⟩

theorem reference_le (s : List Entry)
    (h : ∀ e ∈ s, -1000000000000 ≤ e.x ∧ e.x ≤ 1000000000000) :
    -(1000000000000 * (s.length : Int)) ≤ reference s ∧
      reference s ≤ 1000000000000 * (s.length : Int) := by
  induction s with
  | nil => simp only [reference, List.length_nil]; constructor <;> omega
  | cons e t ih =>
    have he := h e (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [reference, List.length_cons]
    constructor <;> omega

theorem reference_fits : ReferenceFits := by
  unfold ReferenceFits Bounded Fits minInt maxInt
  intro s ⟨hl, hm⟩
  have := reference_le s (fun e he => ⟨(hm e he).1, (hm e he).2.1⟩)
  constructor <;> omega

theorem check_site_fits : CheckSiteFits := by
  unfold CheckSiteFits InRange Fits minInt maxInt
  intro e e' h1 h2
  constructor <;> omega

/-! ## Keeping the invariant by construction: `push` -/

theorem push_eq_some {x : Int} {s s' : List Entry} (h : push x s = some s') :
    -1000000000000 ≤ x ∧ x ≤ 1000000000000 ∧
    -1000000000000000 ≤ x + plan s ∧ x + plan s ≤ 1000000000000000 ∧
    s' = { x, cum := x + plan s } :: s := by
  unfold push at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h
      refine ⟨by omega, by omega, by omega, by omega, rfl⟩

theorem push_preserves_consistent : PushPreservesConsistent := by
  unfold PushPreservesConsistent
  intro x s s' hs h
  obtain ⟨-, -, -, -, rfl⟩ := push_eq_some h
  refine ⟨?_, hs⟩
  simp only [reference]
  rw [plan_correct s hs]

theorem push_tail : PushTail := by
  unfold PushTail
  intro x s s' h
  obtain ⟨-, -, -, -, rfl⟩ := push_eq_some h
  rfl

theorem push_reference : PushReference := by
  unfold PushReference
  intro x s s' h
  obtain ⟨-, -, -, -, rfl⟩ := push_eq_some h
  rfl

theorem push_total : PushTotal := by
  unfold PushTotal
  intro x s s' hs h
  obtain ⟨-, -, -, -, rfl⟩ := push_eq_some h
  show x + plan s = x + reference s
  rw [plan_correct s hs]

theorem plan_values_bounded (s : List Entry) (hs : ValuesBounded s) :
    -1000000000000000 ≤ plan s ∧ plan s ≤ 1000000000000000 := by
  cases s with
  | nil => simp [plan]
  | cons e t =>
    have := hs e (List.mem_cons_self ..)
    simp only [InRange] at this
    simp only [plan]
    constructor <;> omega

theorem push_values_bounded : PushValuesBounded := by
  unfold PushValuesBounded ValuesBounded InRange
  intro x s s' hs h
  obtain ⟨h1, h2, h3, h4, rfl⟩ := push_eq_some h
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨h1, h2, h3, h4⟩
  · exact hs e he

theorem push_site_fits : PushSiteFits := by
  unfold PushSiteFits Fits minInt maxInt
  intro x s hs h1 h2
  have := plan_values_bounded s hs
  constructor <;> omega

theorem push_preserves : PushPreserves := by
  unfold PushPreserves Invariant
  intro x s s' ⟨hc, hb⟩ h
  exact ⟨push_preserves_consistent x s s' hc h, push_values_bounded x s s' hb h⟩

theorem reference_fits_inv : ReferenceFitsInv := by
  unfold ReferenceFitsInv Fits minInt maxInt
  intro s ⟨hinv, hs⟩
  have := plan_values_bounded s hs
  rw [← plan_correct s hinv]
  constructor <;> omega

/-! ## `run`: the fallback is guarded by its own domain check -/

theorem checkBoundedFrom_iff (n : Int) (s : List Entry) (hn : 0 ≤ n) (hn' : n ≤ 1000) :
    checkBoundedFrom n s = true ↔
      n + (s.length : Int) ≤ 1000 ∧ ∀ e ∈ s, -1000000000000 ≤ e.x ∧ e.x ≤ 1000000000000 := by
  induction s generalizing n with
  | nil => simp only [checkBoundedFrom, List.length_nil, List.not_mem_nil, false_implies,
      implies_true, and_true, true_iff]; omega
  | cons e t ih =>
    by_cases hlt : n < 1000
    · simp only [checkBoundedFrom, Bool.and_eq_true, decide_eq_true_eq,
        ih (n + 1) (by omega) (by omega), List.length_cons, List.forall_mem_cons]
      constructor
      · rintro ⟨_, h2, h3, h4, h5⟩
        exact ⟨by omega, ⟨h2, h3⟩, h5⟩
      · rintro ⟨h1, ⟨h2, h3⟩, h5⟩
        exact ⟨hlt, h2, h3, by omega, h5⟩
    · simp only [checkBoundedFrom, Bool.and_eq_true, decide_eq_true_eq, hlt, false_and,
        false_iff, List.length_cons]
      rintro ⟨h, -⟩
      omega

theorem check_bounded_sound : CheckBoundedSound := by
  unfold CheckBoundedSound FallbackDomain checkBounded
  intro s h
  have ⟨h1, h2⟩ := (checkBoundedFrom_iff 0 s (by omega) (by omega)).mp h
  exact ⟨by omega, h2⟩

theorem check_bounded_of_bounded (s : List Entry) (h : Bounded s) : checkBounded s = true := by
  unfold checkBounded
  obtain ⟨hl, hm⟩ := h
  exact (checkBoundedFrom_iff 0 s (by omega) (by omega)).mpr
    ⟨by omega, fun e he => ⟨(hm e he).1, (hm e he).2.1⟩⟩

theorem fallback_domain_tail : FallbackDomainTail := by
  unfold FallbackDomainTail FallbackDomain
  intro e t ⟨hl, hm⟩
  simp only [List.length_cons] at hl
  exact ⟨by omega, fun x hx => hm x (List.mem_cons_of_mem _ hx)⟩

theorem fallback_fits : FallbackFits := by
  unfold FallbackFits FallbackDomain Fits minInt maxInt
  intro s ⟨hl, hm⟩
  have := reference_le s hm
  constructor <;> omega

theorem counter_fits : CounterFits := by
  unfold CounterFits Fits minInt maxInt
  intro n h1 h2
  constructor <;> omega

theorem run_sound : RunSound := by
  unfold RunSound run
  intro s v h
  split at h
  · cases h; exact plan_correct s (check_sound s ‹_›).1
  · split at h
    · cases h; rfl
    · cases h

theorem run_complete : RunComplete := by
  unfold RunComplete run
  intro s hb
  split
  · rw [plan_correct s (check_sound s ‹_›).1]
  · simp only [check_bounded_of_bounded s hb, ↓reduceIte]

end RunningSum
