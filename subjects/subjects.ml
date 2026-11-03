(** Registered examples, as first-class modules for the generic harnesses. *)
type t = (module Harness.Subject.S)

let all : t list = [ (module Running_sum_subject) ]
