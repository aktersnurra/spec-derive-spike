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
  | nil => simp [checkFrom, Consistent, reference]
  | cons e' t ih =>
    simp only [checkFrom, Bool.and_eq_true, beq_iff_eq, inRange_iff, ih, Consistent, reference,
      List.forall_mem_cons]
    constructor
    · rintro ⟨hr, hc, ⟨hc', hct⟩, hall⟩
      exact ⟨⟨by omega, hc', hct⟩, hr, hall⟩
    · rintro ⟨⟨hc, hc', hct⟩, hr, hall⟩
      exact ⟨hr, by omega, ⟨hc', hct⟩, hall⟩

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

theorem run_correct : RunCorrect := by
  unfold RunCorrect run
  intro s
  split
  · exact plan_correct s (check_sound s ‹_›).1
  · rfl

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
  | nil => simp [reference]
  | cons e t ih =>
    have he := h e (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [reference, List.length_cons]
    omega

theorem reference_fits : ReferenceFits := by
  unfold ReferenceFits Bounded Fits minInt maxInt
  intro s ⟨hl, hm⟩
  have := reference_le s (fun e he => ⟨(hm e he).1, (hm e he).2.1⟩)
  omega

theorem check_site_fits : CheckSiteFits := by
  unfold CheckSiteFits InRange Fits minInt maxInt
  intro e e' h1 h2
  omega

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
    omega

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
  omega

theorem push_preserves : PushPreserves := by
  unfold PushPreserves Invariant
  intro x s s' ⟨hc, hb⟩ h
  exact ⟨push_preserves_consistent x s s' hc h, push_values_bounded x s s' hb h⟩

theorem reference_fits_inv : ReferenceFitsInv := by
  unfold ReferenceFitsInv Fits minInt maxInt
  intro s ⟨hinv, hs⟩
  have := plan_values_bounded s hs
  rw [← plan_correct s hinv]
  omega

end RunningSum
