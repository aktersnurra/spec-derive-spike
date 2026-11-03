(* Fair competitors for the generated push/total: hand-written OCaml keeping a running total
   next to the list. No proofs, no generator. *)

(** Plain: no bounds checks, no Option. *)
module Plain = struct
  type t = { total : int; items : int list }

  let empty = { total = 0; items = [] }
  let push x t = { total = t.total + x; items = x :: t.items }
  let total t = t.total
end

(** Same bounds checks and Option result as the generated push. *)
module Checked = struct
  type t = { total : int; items : int list }

  let x_bound = 1_000_000_000_000
  let cum_bound = 1_000_000_000_000_000
  let empty = { total = 0; items = [] }

  let push x t =
    if x < -x_bound || x_bound < x then None
    else
      let total = x + t.total in
      if total < -cum_bound || cum_bound < total then None else Some { total; items = x :: t.items }

  let total t = t.total
end
