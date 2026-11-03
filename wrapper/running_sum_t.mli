(** Running sum whose cached totals are consistent by construction.

    Guarantee: every value of type [t] was produced either by [of_list], which ran the
    generated [check_invariant], or by [push], the generated invariant-preserving
    operation. So [total] can use the O(1) plan with no check.

    What this rests on: Lean proves [check_invariant] sound and [push] preserving for the
    Lean definitions only ([RunningSum.check_sound], [RunningSum.push_preserves]). That the
    generated OCaml matches those definitions is tested, not proved. The type gives no
    protection if the generator is unfaithful, and none for inputs to [of_list] outside the
    spec's [Bounded] domain (not checked). *)

type t = private Gen.Running_sum_gen.entry list

val empty : t

val of_list : Gen.Running_sum_gen.entry list -> t option
(** [Some] iff the generated checker accepts the list. O(n). *)

val push : int -> t -> t option
(** O(1). [None] if the amount or the new total would leave the spec's value bounds. *)

val total : t -> int
(** O(1): the plan, with no check. *)
