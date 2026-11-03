import SpecDerive.RunningSum.Spec

namespace RunningSum

theorem cum_of_invariant {e : Entry} {t : List Entry} (h : Invariant (e :: t)) :
    e.cum = e.x + reference t := by
  simp only [Invariant, reference] at h
  exact h.1

theorem plan_correct : PlanCorrect := by
  unfold PlanCorrect
  intro s h
  cases s with
  | nil => rfl
  | cons e t => simp only [plan, reference]; exact cum_of_invariant h

theorem checkFrom_iff (e : Entry) (t : List Entry) : checkFrom e t = true ↔ Invariant (e :: t) := by
  induction t generalizing e with
  | nil => simp only [checkFrom, beq_iff_eq, Invariant, reference, and_true]; omega
  | cons e' t ih =>
    simp only [checkFrom, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · intro ⟨h1, h2⟩
      have := cum_of_invariant h2
      refine ⟨?_, h2⟩
      simp only [reference] at this ⊢
      omega
    · intro h
      have h1 := cum_of_invariant h
      have h2 := cum_of_invariant h.2
      refine ⟨?_, h.2⟩
      simp only [reference] at h1
      omega

theorem check_sound : CheckSound := by
  unfold CheckSound
  intro s h
  cases s with
  | nil => trivial
  | cons e t => exact (checkFrom_iff e t).mp h

theorem check_complete : CheckComplete := by
  unfold CheckComplete
  intro s h
  cases s with
  | nil => rfl
  | cons e t => exact (checkFrom_iff e t).mpr h

theorem run_correct : RunCorrect := by
  unfold RunCorrect run
  intro s
  split
  · exact plan_correct s (check_sound s ‹_›)
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
  unfold CheckSiteFits Bounded Fits minInt maxInt
  intro e e' t ⟨_, hm⟩
  have h1 := hm e (List.mem_cons_self ..)
  have h2 := hm e' (List.mem_cons_of_mem _ (List.mem_cons_self ..))
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

theorem push_preserves : PushPreserves := by
  unfold PushPreserves
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
    simp only [plan]
    omega

theorem push_values_bounded : PushValuesBounded := by
  unfold PushValuesBounded ValuesBounded
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

theorem reference_fits_inv : ReferenceFitsInv := by
  unfold ReferenceFitsInv Fits minInt maxInt
  intro s hinv hs
  have := plan_values_bounded s hs
  rw [← plan_correct s hinv]
  omega

end RunningSum
