(* Differential test for the three-way generated `run` (running_sum) on any input:
   - Valid: consistent, in range        -> Some reference (plan path)
   - Stale: stale cache, every |x| <= 10^12, <= 1000 entries (cum may be anything,
            including min_int / max_int)  -> Some reference (recomputed)
   - Out:   outside the fallback domain  -> None ("outside the supported domain")
            (|x| > 10^12, exact min_int / max_int amounts, the max_int example, or a stale
            list longer than 1000)
   Each case is compared with Lean's `run` (oracle mode `running_sum_run`), and with the
   expected kind. *)
open Harness
module G = Gen.Running_sum_gen

let x_bound = 1_000_000_000_000
let cum_bound = 1_000_000_000_000_000

let consistent = Push_seq.consistent
let amounts st n = List.init n (fun _ -> Pick.int_in st (-x_bound) x_bound)

(** Make the cache stale: change one entry's cum to a value that breaks consistency. *)
let stale st s =
  let n = List.length s in
  let at = Random.State.int st n in
  List.mapi
    (fun i (e : G.entry) ->
      if i <> at then e
      else
        let cum =
          match Random.State.int st 4 with
          | 0 -> min_int
          | 1 -> max_int
          | 2 -> if e.cum < cum_bound then e.cum + 1 else e.cum - 1
          | _ -> Pick.int_in st (-cum_bound) cum_bound
        in
        { e with cum = (if cum = e.cum then cum + 1 else cum) })
    s

let ext st = if Random.State.bool st then min_int else max_int

let case st =
  match Random.State.int st 8 with
  | 0 -> (`Valid, consistent (amounts st (Pick.size st 1000)))
  | 1 | 2 -> (`Stale, stale st (consistent (amounts st (1 + Pick.size st 999))))
  | 3 ->
      let xs = amounts st (1 + Pick.size st 999) in
      let at = Random.State.int st (List.length xs) in
      let bad = if Random.State.bool st then x_bound + 1 else -x_bound - 1 in
      (`Out, consistent (List.mapi (fun i x -> if i = at then bad else x) xs))
  | 4 -> (`Out, stale st (consistent (amounts st (Pick.int_in st 1001 1010))))
  | 5 -> (`Out, [ { G.x = x_bound; cum = 5 }; { G.x = max_int; cum = 0 } ]) (* the max_int example *)
  | 6 -> let v = ext st in (`Out, [ { G.x = v; cum = v } ])
  | _ -> (`Out, [ { G.x = Pick.int_in st (-x_bound) x_bound; cum = 0 }; { G.x = ext st; cum = ext st } ])

let show = function None -> "none" | Some v -> Printf.sprintf "some %d" v

let run ~oracle ~seed ~cases =
  let st = Random.State.make [| seed; 23 |] in
  let inputs = Array.init cases (fun _ -> case st) in
  let lines = Array.map (fun (_, s) -> Subjects.to_line_running_sum s) inputs in
  let expected =
    Array.of_list (Diff.oracle_outputs ~oracle ~name:"running_sum_run" (Array.to_list lines))
  in
  let failures = ref [] and counts = Hashtbl.create 3 in
  let fail k msg = failures := Printf.sprintf "seed=%d case=%d: %s; input: %s" seed k msg (Diff.shorten lines.(k)) :: !failures in
  Array.iteri
    (fun k (kind, s) ->
      let got = G.run s in
      if show got <> expected.(k) then fail k (Printf.sprintf "OCaml run = %s, Lean run = %s" (show got) expected.(k));
      (match (kind, got) with
      | (`Valid | `Stale), Some v when v = G.reference s -> ()
      | (`Valid | `Stale), _ -> fail k "in-domain input not answered with the reference value"
      | `Out, None -> ()
      | `Out, Some _ -> fail k "out-of-domain input answered");
      Hashtbl.replace counts kind (1 + Option.value ~default:0 (Hashtbl.find_opt counts kind)))
    inputs;
  let count k = Option.value ~default:0 (Hashtbl.find_opt counts k) in
  (List.rev !failures, count `Valid, count `Stale, count `Out)
