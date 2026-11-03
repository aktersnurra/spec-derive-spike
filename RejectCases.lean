/-!
Negative tests for the generator: each definition here is outside the subset and
`lake exe emit reject ...` (see `scripts/test-reject.sh`) must refuse it.
-/
namespace RejectCases

def usesNat (n : Nat) : Nat := n - 1
def usesDiv (a b : Int) : Int := a / b
def usesLength (s : List Int) : Int := s.length
def higherOrder (s : List Int) : List Int := s.map (· + 1)
partial def usesPartial (n : Int) : Int := if n ≤ 0 then 0 else usesPartial (n - 1)
def wellFounded (n : Int) : Int := if h : n ≤ 0 then 0 else wellFounded (n - 1)
termination_by n.toNat
decreasing_by omega
def bigLiteral : Int := 10000000000000000000
def polymorphic {α : Type} (a : α) : α := a
def nonStdInstance (a b : Int) : Int := @HAdd.hAdd _ _ _ (@instHAdd _ ⟨Int.sub⟩) a b
def functionParam (f : Int → Int) (x : Int) : Int := f (f x)
set_option linter.unusedVariables false in
def matchWithHyp (s : List Int) : Int :=
  match h : s with
  | [] => 0
  | _ :: _ => 1
def literalPattern : Int → Int
  | 0 => 1
  | _ => 2

end RejectCases
