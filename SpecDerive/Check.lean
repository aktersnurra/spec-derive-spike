import SpecDerive.RunningSum.Proofs
import SpecDerive.SortedLookup.Proofs

/-! Proof gate: every statement has a proof, and the proofs use only standard axioms. -/

example : RunningSum.PlanCorrect := RunningSum.plan_correct
example : RunningSum.CheckSound := RunningSum.check_sound
example : RunningSum.CheckComplete := RunningSum.check_complete
example : RunningSum.RunCorrect := RunningSum.run_correct
example : RunningSum.BoundedTail := RunningSum.bounded_tail
example : RunningSum.ReferenceFits := RunningSum.reference_fits
example : RunningSum.CheckSiteFits := RunningSum.check_site_fits
example : SortedLookup.PlanCorrect := SortedLookup.plan_correct
example : SortedLookup.CheckSound := SortedLookup.check_sound
example : SortedLookup.CheckComplete := SortedLookup.check_complete
example : SortedLookup.RunCorrect := SortedLookup.run_correct

#print axioms RunningSum.plan_correct
#print axioms RunningSum.check_sound
#print axioms RunningSum.check_complete
#print axioms RunningSum.run_correct
#print axioms RunningSum.bounded_tail
#print axioms RunningSum.reference_fits
#print axioms RunningSum.check_site_fits
#print axioms SortedLookup.plan_correct
#print axioms SortedLookup.check_sound
#print axioms SortedLookup.check_complete
#print axioms SortedLookup.run_correct
