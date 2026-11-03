(* Differential test for building by construction: random push sequences go through the
   typed wrapper (Wrapper.Running_sum_t) and the Lean oracle (`running_sum_push`). For each
   sequence, compares the refusal count, plan total, reference, checker verdict and the full
   list of entries; and checks total = reference in OCaml. This is a sequence-of-operations
   test, which the generic input -> output Diff driver does not express; it reuses
   Diff.oracle_outputs and Pick. *)
open Harness
module G = Gen.Running_sum_gen
module T = Wrapper.Running_sum_t

(* Spec value bounds (RunningSum.push / ValuesBounded): |x| <= 10^12, |cum| <= 10^15. *)
let x_bound = 1_000_000_000_000
let cum_bound = 1_000_000_000_000_000

(** Amount sequences: random in range, saturating at +-x_bound past the cum bound (1000 such
    pushes reach exactly 10^15), or sprinkled with out-of-range amounts. *)
let amounts st =
  match Random.State.int st 6 with
  | 0 -> List.init (Pick.int_in st 995 1010) (fun _ -> x_bound)
  | 1 -> List.init (Pick.int_in st 995 1010) (fun _ -> -x_bound)
  | 2 ->
      List.init (Pick.size st 200) (fun _ ->
          match Random.State.int st 5 with
          | 0 -> x_bound + 1
          | 1 -> -x_bound - 1
          | 4 -> if Random.State.bool st then min_int else max_int
          | 2 -> Pick.int_in st (-1_000_000_000_000_000_000) 1_000_000_000_000_000_000
          | _ -> Pick.int_in st (-x_bound) x_bound)
  | _ -> List.init (Pick.size st 1100) (fun _ -> Pick.int_in st (-x_bound) x_bound)

let build xs =
  List.fold_left
    (fun (t, refused) x -> match T.push x t with Some t' -> (t', refused) | None -> (t, refused + 1))
    (T.empty, 0) xs

let line_of ((t : T.t), refused) =
  let s = (t :> G.entry list) in
  String.concat " "
    ([ string_of_int refused; string_of_int (T.total t); string_of_int (G.reference s);
       string_of_bool (G.check_invariant s) ]
    @ List.map (fun (e : G.entry) -> Printf.sprintf "%d:%d" e.x e.cum) s)

let run ~oracle ~seed ~cases =
  let st = Random.State.make [| seed |] in
  let seqs = Array.init cases (fun _ -> amounts st) in
  let lines = Array.map (fun xs -> String.concat " " (List.map string_of_int xs)) seqs in
  let expected =
    Array.of_list (Diff.oracle_outputs ~oracle ~name:"running_sum_push" (Array.to_list lines))
  in
  let failures = ref [] and refused = ref 0 and at_bound = ref 0 in
  Array.iteri
    (fun k xs ->
      let ((t, r) as built) = build xs in
      refused := !refused + r;
      if abs (T.total t) = cum_bound then incr at_bound;
      let got = line_of built in
      if got <> expected.(k) then
        failures := Printf.sprintf "seed=%d case=%d: OCaml %s; Lean %s" seed k
            (Diff.shorten got) (Diff.shorten expected.(k)) :: !failures;
      if T.total t <> G.reference (t :> G.entry list) then
        failures := Printf.sprintf "seed=%d case=%d: total <> reference" seed k :: !failures)
    seqs;
  (List.rev !failures, !refused, !at_bound)

(* of_list on external lists: consistent caches with values in range (accept), and consistent
   caches with an out-of-range amount, an out-of-range total, or huge values (reject).
   Compares Running_sum_t.of_list with the Lean checker verdict (2nd field of the
   `running_sum` oracle output). *)

(** Consistent entries (newest first) from amounts listed newest first; no bounds applied. *)
let consistent xs =
  List.fold_right
    (fun x acc ->
      match acc with
      | [] -> [ { G.x; cum = x } ]
      | (e : G.entry) :: _ -> { G.x; cum = x + e.cum } :: acc)
    xs []

let external_list st =
  let in_range n = List.init n (fun _ -> Pick.int_in st (-x_bound) x_bound) in
  match Random.State.int st 6 with
  | 0 -> (`Valid, consistent (in_range (Pick.size st 1000)))
  | 5 ->
      (* exact OCaml extremes: a single consistent entry, or an older entry whose x or cum is
         min_int / max_int under an in-range head *)
      let ext () = if Random.State.bool st then min_int else max_int in
      if Random.State.bool st then (let v = ext () in (`Bad, [ { G.x = v; cum = v } ]))
      else
        let e' = if Random.State.bool st then { G.x = ext (); cum = 0 } else { G.x = 0; cum = ext () } in
        (`Bad, [ { G.x = x_bound; cum = Pick.int_in st (-cum_bound) cum_bound }; e' ])
  | 1 ->
      (* one amount just outside |x| <= 10^12, cached totals still consistent *)
      let xs = in_range (1 + Pick.size st 999) in
      let at = Random.State.int st (List.length xs) in
      let bad = if Random.State.bool st then x_bound + 1 else -x_bound - 1 in
      (`Bad, consistent (List.mapi (fun i x -> if i = at then bad else x) xs))
  | 2 ->
      (* every amount in range, but the running total passes +-10^15 *)
      let x = if Random.State.bool st then x_bound else -x_bound in
      (`Bad, consistent (List.init (Pick.int_in st 1001 1010) (fun _ -> x)))
  | 3 ->
      (* huge consistent values *)
      let big = Pick.int_in st 1_000_000_000_000_000_000 4_000_000_000_000_000_000 in
      (`Bad, consistent [ Pick.int_in st (-x_bound) x_bound; big ])
  | _ ->
      (* older entry near max_int: the unguarded e.x + e'.cum would overflow *)
      let e' = { G.x = max_int - 7; cum = max_int - 7 } in
      (`Bad, [ { G.x = x_bound; cum = Pick.int_in st (-cum_bound) cum_bound }; e' ])

let run_of_list ~oracle ~seed ~cases =
  let st = Random.State.make [| seed; 17 |] in
  let lists = Array.init cases (fun _ -> external_list st) in
  let lines = Array.map (fun (_, s) -> Subjects.to_line_running_sum s) lists in
  let expected =
    Array.of_list (Diff.oracle_outputs ~oracle ~name:"running_sum" (Array.to_list lines))
  in
  let failures = ref [] and accepted = ref 0 and rejected_bad = ref 0 in
  Array.iteri
    (fun k (kind, s) ->
      let ok = Option.is_some (T.of_list s) in
      let lean = List.nth (String.split_on_char ' ' expected.(k)) 1 in
      if string_of_bool ok <> lean then
        failures := Printf.sprintf "seed=%d case=%d: of_list accepts=%b, Lean checker=%s; input: %s"
            seed k ok lean (Diff.shorten lines.(k)) :: !failures;
      (match (kind, ok) with
      | `Valid, true -> incr accepted
      | `Bad, false -> incr rejected_bad
      | `Valid, false ->
          failures := Printf.sprintf "seed=%d case=%d: valid list rejected" seed k :: !failures
      | `Bad, true ->
          failures := Printf.sprintf "seed=%d case=%d: out-of-range list accepted" seed k :: !failures))
    lists;
  (List.rev !failures, !accepted, !rejected_bad)
