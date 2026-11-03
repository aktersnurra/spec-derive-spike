/-!
# Lookup in a key-sorted association list, with early exit

The reference scans until it finds the key, so a miss walks the whole list. If keys are
strictly increasing, a miss can stop at the first key greater than the query.
-/

namespace SortedLookup

/-- One association: `key` maps to `value`. -/
structure Entry where
  key : Int
  value : Int

/-- Reference: value of the first entry with key `k`. Obviously correct; a miss is O(n). -/
def reference : List Entry → Int → Option Int
  | [], _ => none
  | e :: t, k => if e.key = k then some e.value else reference t k

/-- Invariant (Prop): keys are strictly increasing. -/
def Invariant (s : List Entry) : Prop := s.Pairwise (fun a b => a.key < b.key)

/-- Checker helper: `e`'s key is below the next key, and so on down the list. -/
def checkFrom : Entry → List Entry → Bool
  | _, [] => true
  | e, e' :: t => decide (e.key < e'.key) && checkFrom e' t

/-- Invariant checker, O(n): adjacent keys strictly increase. -/
def checkInvariant : List Entry → Bool
  | [] => true
  | e :: t => checkFrom e t

/-- Plan: stop at the first key greater than `k`. Correct only under `Invariant`. -/
def plan : List Entry → Int → Option Int
  | [], _ => none
  | e :: t, k => if k < e.key then none else if e.key = k then some e.value else plan t k

/-- Runtime entry point: use the plan only when its proof's assumption holds.
Precondition (not checked): `Bounded s k`. -/
def run (s : List Entry) (k : Int) : Option Int :=
  if checkInvariant s then plan s k else reference s k

/-! ## Statements (proved in `Proofs.lean`) -/

/-- (a) The invariant licenses the plan. -/
def PlanCorrect : Prop := ∀ s k, Invariant s → plan s k = reference s k

/-- (b) The Bool checker is sound w.r.t. the Prop invariant. -/
def CheckSound : Prop := ∀ s, checkInvariant s = true → Invariant s

/-- (b) The Bool checker is complete w.r.t. the Prop invariant. -/
def CheckComplete : Prop := ∀ s, Invariant s → checkInvariant s = true

/-- `run` agrees with the reference on every input. -/
def RunCorrect : Prop := ∀ s k, run s k = reference s k

/-! ## Integer bounds

The emitted functions contain no Int arithmetic sites (comparisons only; the generator's
header confirms this), and every result is an input value. So the only obligation is that
inputs are representable as OCaml ints, which `Bounded` states directly; there is nothing
further to prove. The 10^15 bound (rather than ±2^62) keeps the test generators simple. -/

/-- Input domain of the generated OCaml: at most 1000 entries, keys, values and the query
within ±10^15. -/
def Bounded (s : List Entry) (k : Int) : Prop :=
  s.length ≤ 1000 ∧ -1000000000000000 ≤ k ∧ k ≤ 1000000000000000 ∧
  ∀ e ∈ s, -1000000000000000 ≤ e.key ∧ e.key ≤ 1000000000000000 ∧
           -1000000000000000 ≤ e.value ∧ e.value ≤ 1000000000000000

instance (s : List Entry) (k : Int) : Decidable (Bounded s k) := by
  unfold Bounded; infer_instance

end SortedLookup
