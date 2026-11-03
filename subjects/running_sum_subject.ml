(** Adapter: generated running-sum module + input generation + oracle line format. *)
module G = Gen.Running_sum_gen
open Harness

type input = G.entry list
type output = int

let name = "running_sum"
let max_size = 1000
let reference = G.reference
let plan = G.plan
let check_invariant = G.check_invariant
let run = G.run
let equal_output = Int.equal
let show_output = string_of_int

let to_line s =
  String.concat " " (List.map (fun (e : G.entry) -> Printf.sprintf "%d:%d" e.x e.cum) s)

(* Spec bounds (RunningSum.Bounded): |x| <= 10^12, |cum| <= 10^15. *)
let x_bound = 1_000_000_000_000
let cum_bound = 1_000_000_000_000_000

(** Entries with consistent cached totals, from amounts listed newest first. *)
let consistent xs =
  List.fold_right
    (fun x acc ->
      match acc with
      | [] -> [ { G.x; cum = x } ]
      | (e : G.entry) :: _ -> { G.x; cum = x + e.cum } :: acc)
    xs []

let amounts st ~size =
  match Random.State.int st 10 with
  | 0 -> List.init size (fun _ -> x_bound) (* drives cum to the bound *)
  | 1 -> List.init size (fun _ -> -x_bound)
  | _ -> List.init size (fun _ -> Pick.int_in st (-x_bound) x_bound)

(** Break the invariant: one cum off by one, one cum random, or every cum random. *)
let corrupt st s =
  let n = List.length s in
  if n = 0 then s
  else
    let at = Random.State.int st n in
    let mode = Random.State.int st 3 in
    List.mapi
      (fun k (e : G.entry) ->
        let cum' = if e.cum < cum_bound then e.cum + 1 else e.cum - 1 in
        match mode with
        | 0 when k = at -> { e with cum = cum' }
        | 1 when k = at -> { e with cum = Pick.int_in st (-cum_bound) cum_bound }
        | 2 -> { e with cum = Pick.int_in st (-cum_bound) cum_bound }
        | _ -> e)
      s

let gen st ~size ~valid =
  let s = consistent (amounts st ~size) in
  if valid then s else corrupt st s

let workload st ~size =
  consistent (List.init size (fun _ -> Random.State.full_int st (2 * x_bound + 1) - x_bound))
