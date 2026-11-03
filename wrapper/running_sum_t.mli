(** Running sum whose invariant holds by construction.

    Guarantee: every value of type [t] satisfies the spec's [RunningSum.Invariant], which is
    cache consistency AND value bounds (every |x| <= 10^12, every cached total within
    +-10^15). This holds because the only ways to make a [t] are:
    - [empty] (trivially consistent and in range);
    - [of_list], which runs the generated [check_invariant]. In Lean, [check_sound] proves the
      checker accepts only consistent, in-range lists. The checker range-checks each entry
      before using it in arithmetic, so [of_list] is safe on any input list, with no
      precondition;
    - [push], the generated operation that [push_preserves] proves keeps the invariant. It
      returns [None] rather than leave the bounds.

    Consequences: [total] is the O(1) plan with no check, equal to the recomputed sum
    ([plan_correct]). No operation on [t] can overflow an OCaml int ([push_site_fits],
    [check_site_fits]).

    Still trusted (not proved):
    - The proofs cover the Lean definitions only. That the generated OCaml matches them is
      tested (differential tests against a Lean oracle), not proved.
    - That [check_from] range-checks an entry before the addition that uses it. This is
      read off the code order and [&&] short-circuiting, not proved.
    - The OCaml compiler, and this file (6 lines). *)

type t = private Gen.Running_sum_gen.entry list

val empty : t

val of_list : Gen.Running_sum_gen.entry list -> t option
(** [Some] iff the list is consistent and in range (the generated checker). O(n). Safe on any
    input. *)

val push : int -> t -> t option
(** O(1). [None] if the amount or the new total would leave the value bounds. *)

val total : t -> int
(** O(1): the plan, with no check. *)
