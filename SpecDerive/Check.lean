import SpecDerive.RunningSum.Proofs

/-! Proof gate: every statement has a proof, and the proofs use only standard axioms. -/

example : RunningSum.PlanCorrect := RunningSum.plan_correct
example : RunningSum.CheckSound := RunningSum.check_sound
example : RunningSum.CheckComplete := RunningSum.check_complete
example : RunningSum.RunCorrect := RunningSum.run_correct
example : RunningSum.BoundedTail := RunningSum.bounded_tail
example : RunningSum.ReferenceFits := RunningSum.reference_fits
example : RunningSum.CheckSiteFits := RunningSum.check_site_fits

#print axioms RunningSum.plan_correct
#print axioms RunningSum.check_sound
#print axioms RunningSum.check_complete
#print axioms RunningSum.run_correct
#print axioms RunningSum.bounded_tail
#print axioms RunningSum.reference_fits
#print axioms RunningSum.check_site_fits
