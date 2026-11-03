(** What the generic harnesses need from one reference / invariant / plan example.
    The generated module provides [reference], [plan], [check_invariant], [run]; a small
    hand-written adapter adds input generation and the oracle line format. *)
module type S = sig
  type input
  type output

  val name : string
  (** Example name, as understood by the Lean oracle. *)

  val max_size : int
  (** Largest input size inside the spec's [Bounded] domain. *)

  val reference : input -> output
  val plan : input -> output
  val check_invariant : input -> bool
  val run : input -> output option
  (** [None] means the input is outside the example's supported domain (not "invalid"). *)

  val equal_output : output -> output -> bool

  val show_output : output -> string
  (** Must print exactly like the Lean oracle prints the reference result. *)

  val to_line : input -> string
  (** One oracle input line. *)

  val gen : Random.State.t -> size:int -> valid:bool -> input
  (** Random input of [size] inside [Bounded], boundary-biased via {!Pick}.
      [valid:true] builds an input satisfying the invariant; [valid:false] tries to break it. *)

  val workload : Random.State.t -> size:int -> input
  (** Benchmark input of [size] satisfying the invariant (the case the plan is licensed for). *)
end
