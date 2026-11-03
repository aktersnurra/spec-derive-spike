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
          match Random.State.int st 4 with
          | 0 -> x_bound + 1
          | 1 -> -x_bound - 1
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
