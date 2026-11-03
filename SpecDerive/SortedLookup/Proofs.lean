import SpecDerive.SortedLookup.Spec

namespace SortedLookup

theorem reference_none_of_lt (k : Int) (t : List Entry) (h : ∀ e ∈ t, k < e.key) :
    reference t k = none := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    have he := h e (List.mem_cons_self ..)
    simp only [reference]
    rw [if_neg (by omega)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem plan_correct : PlanCorrect := by
  unfold PlanCorrect Invariant
  intro s k h
  induction s with
  | nil => rfl
  | cons e t ih =>
    rw [List.pairwise_cons] at h
    simp only [plan, reference]
    by_cases hlt : k < e.key
    · rw [if_pos hlt, if_neg (by omega)]
      exact (reference_none_of_lt k t (fun x hx => Int.lt_trans hlt (h.1 x hx))).symm
    · rw [if_neg hlt]
      by_cases heq : e.key = k
      · rw [if_pos heq, if_pos heq]
      · rw [if_neg heq, if_neg heq]
        exact ih h.2

theorem checkFrom_iff (e : Entry) (t : List Entry) :
    checkFrom e t = true ↔ Invariant (e :: t) := by
  unfold Invariant
  induction t generalizing e with
  | nil => simp [checkFrom]
  | cons e' t ih =>
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · intro ⟨h1, h2⟩
      rw [List.pairwise_cons] at h2 ⊢
      refine ⟨?_, List.pairwise_cons.mpr h2⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1
      · exact Int.lt_trans h1 (h2.1 x hx)
    · intro h
      rw [List.pairwise_cons] at h
      exact ⟨h.1 e' (List.mem_cons_self ..), h.2⟩

theorem check_sound : CheckSound := by
  unfold CheckSound
  intro s h
  cases s with
  | nil => exact List.Pairwise.nil
  | cons e t => exact (checkFrom_iff e t).mp h

theorem check_complete : CheckComplete := by
  unfold CheckComplete
  intro s h
  cases s with
  | nil => rfl
  | cons e t => exact (checkFrom_iff e t).mpr h

theorem run_correct : RunCorrect := by
  unfold RunCorrect run
  intro s k
  split
  · exact plan_correct s k (check_sound s ‹_›)
  · rfl

end SortedLookup
