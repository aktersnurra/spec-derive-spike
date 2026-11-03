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

theorem check_sound : CheckSound := by
  unfold CheckSound
  intro s
  induction s with
  | nil => intro _; simp [Invariant]
  | cons e t ih =>
    intro h
    cases t with
    | nil =>
      simp only [checkInvariant, beq_iff_eq] at h
      simp only [Invariant, reference, and_true]
      omega
    | cons e' t' =>
      simp only [checkInvariant, Bool.and_eq_true, beq_iff_eq] at h
      have hinv := ih h.2
      have h' := cum_of_invariant hinv
      refine ⟨?_, hinv⟩
      simp only [reference]
      omega

theorem check_complete : CheckComplete := by
  unfold CheckComplete
  intro s
  induction s with
  | nil => intro _; rfl
  | cons e t ih =>
    intro h
    have he := cum_of_invariant h
    have ht : Invariant t := h.2
    cases t with
    | nil =>
      simp only [reference] at he
      simp only [checkInvariant, beq_iff_eq]
      omega
    | cons e' t' =>
      have he' := cum_of_invariant ht
      simp only [checkInvariant, Bool.and_eq_true, beq_iff_eq]
      refine ⟨?_, ih ht⟩
      simp only [reference] at he
      omega

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

end RunningSum
