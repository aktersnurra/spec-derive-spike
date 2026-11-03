/-!
# Running sum with a cached total

A ledger is a list of entries, newest first. Each entry carries an amount `x` and a cached
running total `cum` (this entry plus every older entry). The reference recomputes the total in
O(n); the plan reads the cached total from the head in O(1). The invariant says every cached
total is consistent, which licenses the plan.

Everything in this file except the `Prop` statements is in the generator's subset and is
emitted to OCaml by `Emit.lean`.
-/

namespace RunningSum

/-- One ledger entry: amount `x` and cached total `cum` of this and all older entries. -/
structure Entry where
  x : Int
  cum : Int

/-- Reference: recompute the total. Obviously correct, O(n). -/
def reference : List Entry → Int
  | [] => 0
  | e :: t => e.x + reference t

/-- Invariant (Prop): every cached total equals the recomputed total of its suffix. -/
def Invariant : List Entry → Prop
  | [] => True
  | e :: t => e.cum = reference (e :: t) ∧ Invariant t

/-- Checker helper: entry `e` followed by the older entries `t`. Head and tail are passed
separately so the recursion never rebuilds a list cell (the benchmark showed the earlier
`checkInvariant (e' :: t)` formulation allocating 3 words per entry). -/
def checkFrom : Entry → List Entry → Bool
  | e, [] => e.cum == e.x
  | e, e' :: t => e.cum == e.x + e'.cum && checkFrom e' t

/-- Invariant checker, O(n), no allocation: each `cum` is its `x` plus the next older
entry's `cum`; the oldest entry's `cum` is its `x`. -/
def checkInvariant : List Entry → Bool
  | [] => true
  | e :: t => checkFrom e t

/-- Plan: read the cached total at the head, O(1). Correct only under `Invariant`. -/
def plan : List Entry → Int
  | [] => 0
  | e :: _ => e.cum

/-- Runtime entry point: use the plan only when its proof's assumption holds.
Precondition (not checked): `Bounded s`, so OCaml native ints cannot overflow. -/
def run (s : List Entry) : Int :=
  if checkInvariant s then plan s else reference s

/-- Insert a new newest entry with amount `x` in O(1), keeping the invariant true by
construction: the new cached total is `x` plus the old head's (`plan s`). Refuses (`none`)
when `x` or the new total would leave the value bounds, so a long run of pushes cannot
overflow an OCaml int. `x` is range-checked before the addition is evaluated. -/
def push (x : Int) (s : List Entry) : Option (List Entry) :=
  if x < -1000000000000 ∨ 1000000000000 < x then none
  else
    let cum := x + plan s
    if cum < -1000000000000000 ∨ 1000000000000000 < cum then none
    else some ({ x, cum } :: s)

/-! ## Statements (proved in `Proofs.lean`) -/

/-- (a) The invariant licenses the plan. -/
def PlanCorrect : Prop := ∀ s, Invariant s → plan s = reference s

/-- (b) The Bool checker is sound w.r.t. the Prop invariant. -/
def CheckSound : Prop := ∀ s, checkInvariant s = true → Invariant s

/-- (b) The Bool checker is complete w.r.t. the Prop invariant. -/
def CheckComplete : Prop := ∀ s, Invariant s → checkInvariant s = true

/-- `run` agrees with the reference on every input. -/
def RunCorrect : Prop := ∀ s, run s = reference s

/-- `push` keeps the invariant: lists built by `push` never need checking. -/
def PushPreserves : Prop := ∀ x s s', Invariant s → push x s = some s' → Invariant s'

/-- `push` prepends exactly one entry and leaves the rest of the list unchanged. -/
def PushTail : Prop := ∀ x s s', push x s = some s' → s'.tail = s

/-- `push` adds `x` to the reference total (no invariant needed). -/
def PushReference : Prop := ∀ x s s', push x s = some s' → reference s' = x + reference s

/-- After a push onto a consistent list, the O(1) plan returns the old total plus `x`. -/
def PushTotal : Prop := ∀ x s s', Invariant s → push x s = some s' → plan s' = x + reference s

/-! ## Integer bounds: the gap between Lean `Int` and OCaml `int`

Lean `Int` is unbounded; OCaml `int` on 64-bit is 63-bit two's complement:
`min_int = -2^62`, `max_int = 2^62 - 1`. The generated code is only meaningful on inputs
where every intermediate value fits. `Bounded` is the input domain; the theorems below show
every Int arithmetic site in the emitted functions stays in range on that domain.

Arithmetic sites (the generator lists them in the generated file header):
* `reference`: `e.x + reference t`. Operands: `e.x` (bounded input), `reference t`
  (`ReferenceFits` on the suffix, which is `Bounded` by `BoundedTail`). Result:
  `reference (e :: t)` (`ReferenceFits`).
* `checkFrom`: `e.x + e'.cum`, evaluated for each suffix `e :: e' :: t` of the input
  (`CheckSiteFits`, with `BoundedTail` for the suffix).
* `push`: `x + plan s`, evaluated only after `|x| ≤ 10^12` is checked (`PushSiteFits`).
* `plan`, `run`: none.

Lists built by `push` satisfy `Invariant` and `ValuesBounded` but may be longer than 1000.
`ReferenceFitsInv` shows the length bound is not needed under the invariant: every value
`reference` computes is then a cached total of some suffix. -/

def minInt : Int := -4611686018427387904   -- -2^62
def maxInt : Int := 4611686018427387903    -- 2^62 - 1

def Fits (v : Int) : Prop := minInt ≤ v ∧ v ≤ maxInt

/-- Input domain of the generated OCaml: at most 1000 entries, |x| ≤ 10^12, |cum| ≤ 10^15. -/
def Bounded (s : List Entry) : Prop :=
  s.length ≤ 1000 ∧
  ∀ e ∈ s, -1000000000000 ≤ e.x ∧ e.x ≤ 1000000000000 ∧
           -1000000000000000 ≤ e.cum ∧ e.cum ≤ 1000000000000000

instance (s : List Entry) : Decidable (Bounded s) := by unfold Bounded; infer_instance

/-- The value part of `Bounded`, without the length bound. -/
def ValuesBounded (s : List Entry) : Prop :=
  ∀ e ∈ s, -1000000000000 ≤ e.x ∧ e.x ≤ 1000000000000 ∧
           -1000000000000000 ≤ e.cum ∧ e.cum ≤ 1000000000000000

/-- Recursion stays in the domain: the tail of a bounded list is bounded. -/
def BoundedTail : Prop := ∀ e t, Bounded (e :: t) → Bounded t

/-- Every value `reference` computes on a bounded input fits in an OCaml int. -/
def ReferenceFits : Prop := ∀ s, Bounded s → Fits (reference s)

/-- The one arithmetic site in `checkFrom` fits in an OCaml int. -/
def CheckSiteFits : Prop := ∀ e e' t, Bounded (e :: e' :: t) → Fits (e.x + e'.cum)

/-- `push` keeps every value in range (it refuses instead of leaving the domain). -/
def PushValuesBounded : Prop :=
  ∀ x s s', ValuesBounded s → push x s = some s' → ValuesBounded s'

/-- The one arithmetic site in `push` fits, given the range check that guards it. -/
def PushSiteFits : Prop :=
  ∀ x s, ValuesBounded s → -1000000000000 ≤ x → x ≤ 1000000000000 → Fits (x + plan s)

/-- Under the invariant, `reference` fits for value-bounded lists of any length. -/
def ReferenceFitsInv : Prop := ∀ s, Invariant s → ValuesBounded s → Fits (reference s)

end RunningSum
