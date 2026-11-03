(** Registered examples, as first-class modules for the generic harnesses. *)
type t = (module Harness.Subject.S)

let all : t list = [ (module Running_sum_subject); (module Sorted_lookup_subject) ]

(** Oracle line for a running-sum list (exposed for the by-construction tests). *)
let to_line_running_sum = Running_sum_subject.to_line
