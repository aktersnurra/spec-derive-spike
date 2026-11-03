/-!
# Running sum with a cached total

A ledger is a list of entries, newest first. Each entry carries an amount `x` and a cached
running total `cum` (this entry plus every older entry). The reference recomputes the total in
O(n); the plan reads the cached total from the head in O(1). Cache consistency licenses the
plan. The invariant is consistency plus value bounds, so a list that passed the checker (or
was built by `push`) also cannot overflow an OCaml int.

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

/-- Value bounds for one entry (Prop): |x| ≤ 10^12 and |cum| ≤ 10^15. -/
def InRange (e : Entry) : Prop :=
  -1000000000000 ≤ e.x ∧ e.x ≤ 1000000000000 ∧
  -1000000000000000 ≤ e.cum ∧ e.cum ≤ 1000000000000000

/-- Every entry is in range. -/
def ValuesBounded (s : List Entry) : Prop := ∀ e ∈ s, InRange e

/-- Cache consistency (Prop): every cached total equals the recomputed total of its suffix. -/
def Consistent : List Entry → Prop
  | [] => True
  | e :: t => e.cum = reference (e :: t) ∧ Consistent t

/-- Invariant (Prop): cached totals are consistent and every value is in range. The bounds
are part of the invariant so that a checked or `push`-built list needs no unchecked
precondition. -/
def Invariant (s : List Entry) : Prop := Consistent s ∧ ValuesBounded s

/-- Range check for one entry. Comparisons only, so it is safe on any OCaml int. -/
def inRange (e : Entry) : Bool :=
  -1000000000000 ≤ e.x && (e.x ≤ 1000000000000 &&
    (-1000000000000000 ≤ e.cum && e.cum ≤ 1000000000000000))

/-- Checker helper: `e` (already range-checked) followed by the older entries `t`. Each entry
is range-checked before it is used in arithmetic, so `e.x + e'.cum` is only evaluated on
in-range values. Head and tail are passed separately so the recursion never rebuilds a list
cell (the benchmark showed `checkInvariant (e' :: t)` allocating 3 words per entry). -/
def checkFrom : Entry → List Entry → Bool
  | e, [] => e.cum == e.x
  | e, e' :: t => inRange e' && (e.cum == e.x + e'.cum && checkFrom e' t)

/-- Invariant checker, O(n), no allocation, tail-recursive: every entry is in range, each
`cum` is its `x` plus the next older entry's `cum`, and the oldest entry's `cum` is its `x`. -/
def checkInvariant : List Entry → Bool
  | [] => true
  | e :: t => inRange e && checkFrom e t

/-- Plan: read the cached total at the head, O(1). Correct whenever the cache is consistent. -/
def plan : List Entry → Int
  | [] => 0
  | e :: _ => e.cum

/-- Domain check for the fallback, counting entries with `n`: at most 1000 entries and every
|x| ≤ 10^12. (`reference` never reads `cum`, so `cum` is not checked.) `n + 1` is evaluated only
after `n < 1000` passes. -/
def checkBoundedFrom (n : Int) : List Entry → Bool
  | [] => true
  | e :: t => n < 1000 && (-1000000000000 ≤ e.x && (e.x ≤ 1000000000000 &&
      checkBoundedFrom (n + 1) t))

/-- The fallback's domain check: is it safe to recompute with `reference`? O(n). -/
def checkBounded (s : List Entry) : Bool := checkBoundedFrom 0 s

/-- Runtime entry point, safe on any input:
* invariant holds: the O(1) plan;
* stale cache but the input is in the fallback's domain (`checkBounded`): recompute with
  `reference`;
* otherwise `none`. `none` means "outside the supported domain" (recomputing could overflow
  an OCaml int), not "invalid": the Lean total exists, the generated code cannot compute it. -/
def run (s : List Entry) : Option Int :=
  if checkInvariant s then some (plan s)
  else if checkBounded s then some (reference s)
  else none

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

/-- (a) Cache consistency alone licenses the plan; the bounds are not needed for this. -/
def PlanCorrect : Prop := ∀ s, Consistent s → plan s = reference s

/-- (b) The Bool checker is sound: it accepts only consistent, in-range lists. -/
def CheckSound : Prop := ∀ s, checkInvariant s = true → Invariant s

/-- (b) The Bool checker is complete: it accepts every consistent, in-range list. -/
def CheckComplete : Prop := ∀ s, Invariant s → checkInvariant s = true

/-- `run` never gives a wrong answer: any value it returns is the reference total. -/
def RunSound : Prop := ∀ s v, run s = some v → v = reference s


/-- `push` keeps the full invariant (consistency and bounds): lists built by `push` never
need checking. -/
def PushPreserves : Prop := ∀ x s s', Invariant s → push x s = some s' → Invariant s'

/-- `push` keeps cache consistency, with no assumption about bounds. -/
def PushPreservesConsistent : Prop :=
  ∀ x s s', Consistent s → push x s = some s' → Consistent s'

/-- `push` prepends exactly one entry and leaves the rest of the list unchanged. -/
def PushTail : Prop := ∀ x s s', push x s = some s' → s'.tail = s

/-- `push` adds `x` to the reference total (no invariant needed). -/
def PushReference : Prop := ∀ x s s', push x s = some s' → reference s' = x + reference s

/-- After a push onto a consistent list, the O(1) plan returns the old total plus `x`. -/
def PushTotal : Prop :=
  ∀ x s s', Consistent s → push x s = some s' → plan s' = x + reference s

/-! ## Integer bounds: the gap between Lean `Int` and OCaml `int`

Lean `Int` is unbounded; OCaml `int` on 64-bit is 63-bit two's complement:
`min_int = -2^62`, `max_int = 2^62 - 1`. Every Int arithmetic site in the emitted functions
must stay in range.

Arithmetic sites (the generator lists them in the generated file header):
* `reference`: `e.x + reference t`. Needs the precondition `Bounded` (it runs on arbitrary
  input as `run`'s fallback): `ReferenceFits`, with `BoundedTail` for the recursion. Under the
  invariant, at any length: `ReferenceFitsInv`.
* `checkFrom`: `e.x + e'.cum`. No precondition: `checkInvariant` checks `inRange e` before
  calling `checkFrom e`, and `checkFrom` checks `inRange e'` before evaluating the addition
  (`&&` short-circuits). So both operands are in range (`CheckSiteFits`). That ordering is
  read off the code, not proved.
* `checkBoundedFrom`: `n + 1`, evaluated only after `n < 1000` passes, with `n` starting at 0
  (`CounterFits`; the guard order is read off the code).
* `push`: `x + plan s`, evaluated only after `|x| ≤ 10^12` is checked; `plan s` is in range
  when `ValuesBounded s`, which the invariant includes (`PushSiteFits`).
* `plan`, `run`, `inRange`, `checkBounded`: none.

`run` calls `reference` only when `checkBounded` passed: `CheckBoundedSound` gives
`FallbackDomain`, `FallbackFits` bounds the result, and `FallbackDomainTail` covers the
recursion. -/

def minInt : Int := -4611686018427387904   -- -2^62
def maxInt : Int := 4611686018427387903    -- 2^62 - 1

def Fits (v : Int) : Prop := minInt ≤ v ∧ v ≤ maxInt

/-- Input domain of `reference` (and so `run`): at most 1000 entries, |x| ≤ 10^12,
|cum| ≤ 10^15. -/
def Bounded (s : List Entry) : Prop :=
  s.length ≤ 1000 ∧
  ∀ e ∈ s, -1000000000000 ≤ e.x ∧ e.x ≤ 1000000000000 ∧
           -1000000000000000 ≤ e.cum ∧ e.cum ≤ 1000000000000000

instance (s : List Entry) : Decidable (Bounded s) := by unfold Bounded; infer_instance

/-- The domain `reference` needs: at most 1000 entries and every |x| ≤ 10^12. -/
def FallbackDomain (s : List Entry) : Prop :=
  s.length ≤ 1000 ∧ ∀ e ∈ s, -1000000000000 ≤ e.x ∧ e.x ≤ 1000000000000

/-- The fallback's domain check is sound. -/
def CheckBoundedSound : Prop := ∀ s, checkBounded s = true → FallbackDomain s

/-- Recursion in `reference` stays in the fallback domain. -/
def FallbackDomainTail : Prop := ∀ e t, FallbackDomain (e :: t) → FallbackDomain t

/-- Every value `reference` computes on the fallback domain fits in an OCaml int. -/
def FallbackFits : Prop := ∀ s, FallbackDomain s → Fits (reference s)

/-- The counter in `checkBoundedFrom` fits: it starts at 0 and `n + 1` is evaluated only
when `n < 1000`. -/
def CounterFits : Prop := ∀ n : Int, 0 ≤ n → n < 1000 → Fits (n + 1)

/-- `run` never refuses inside the documented domain. -/
def RunComplete : Prop := ∀ s, Bounded s → run s = some (reference s)

/-- Recursion stays in the domain: the tail of a bounded list is bounded. -/
def BoundedTail : Prop := ∀ e t, Bounded (e :: t) → Bounded t

/-- Every value `reference` computes on a bounded input fits in an OCaml int. -/
def ReferenceFits : Prop := ∀ s, Bounded s → Fits (reference s)

/-- The one arithmetic site in `checkFrom` fits, given the range checks that guard it. -/
def CheckSiteFits : Prop := ∀ e e', InRange e → InRange e' → Fits (e.x + e'.cum)

/-- `push` keeps every value in range (it refuses instead of leaving the domain). -/
def PushValuesBounded : Prop :=
  ∀ x s s', ValuesBounded s → push x s = some s' → ValuesBounded s'

/-- The one arithmetic site in `push` fits, given the range check that guards it. -/
def PushSiteFits : Prop :=
  ∀ x s, ValuesBounded s → -1000000000000 ≤ x → x ≤ 1000000000000 → Fits (x + plan s)

/-- Under the invariant, `reference` fits at any length. -/
def ReferenceFitsInv : Prop := ∀ s, Invariant s → Fits (reference s)

end RunningSum
