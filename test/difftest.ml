(* Differential test of the generated OCaml against the Lean oracle.
   Environment: ORACLE (required, path to the Lean oracle binary), SEED (default 42),
   CASES per example (default 2000). Run via scripts/difftest.sh. *)
open Harness

let env_int name default =
  match Sys.getenv_opt name with Some v -> int_of_string v | None -> default

let oracle =
  match Sys.getenv_opt "ORACLE" with
  | Some p -> p
  | None -> failwith "set ORACLE to the Lean oracle binary (see scripts/difftest.sh)"

let seed = env_int "SEED" 42
let cases = env_int "CASES" 2000

let test_case (module S : Subject.S) =
  Alcotest.test_case S.name `Quick (fun () ->
      let r = Diff.run (module S) ~oracle ~seed ~cases in
      Printf.printf "%s: seed=%d cases=%d invariant held=%d broken=%d plan-alone-wrong=%d\n%!"
        S.name seed r.cases r.invariant_held r.invariant_broken r.plan_differs_when_broken;
      Alcotest.(check (list string)) "no mismatches" [] (List.filteri (fun i _ -> i < 5) r.failures);
      Alcotest.(check bool) "invariant-holding inputs exercised" true (r.invariant_held > cases / 4);
      Alcotest.(check bool) "invariant-violating inputs exercised" true (r.invariant_broken > cases / 4);
      Alcotest.(check bool) "violations that the plan gets wrong exercised" true
        (r.plan_differs_when_broken > 0))

let push_case =
  Alcotest.test_case "running_sum push sequences" `Quick (fun () ->
      let cases = max 1 (cases / 4) in
      let failures, refused, at_bound = Push_seq.run ~oracle ~seed ~cases in
      Printf.printf "push sequences: seed=%d cases=%d refused pushes=%d totals at +-10^15=%d\n%!"
        seed cases refused at_bound;
      Alcotest.(check (list string)) "no mismatches" [] (List.filteri (fun i _ -> i < 5) failures);
      Alcotest.(check bool) "refusals exercised" true (refused > 0);
      Alcotest.(check bool) "totals at the bound exercised" true (at_bound > 0))

let of_list_case =
  Alcotest.test_case "running_sum of_list on external lists" `Quick (fun () ->
      let cases = max 1 (cases / 4) in
      let failures, accepted, rejected = Push_seq.run_of_list ~oracle ~seed ~cases in
      Printf.printf "of_list: seed=%d cases=%d accepted valid=%d rejected out-of-range=%d\n%!" seed
        cases accepted rejected;
      Alcotest.(check (list string)) "no mismatches" [] (List.filteri (fun i _ -> i < 5) failures);
      Alcotest.(check bool) "valid lists exercised" true (accepted > 0);
      Alcotest.(check bool) "out-of-range lists exercised" true (rejected > 0))

let run_case =
  Alcotest.test_case "running_sum run on any input" `Quick (fun () ->
      let cases = max 1 (cases / 4) in
      let failures, valid, stale, out = Run_domain.run ~oracle ~seed ~cases in
      Printf.printf "run: seed=%d cases=%d valid=%d stale-in-domain=%d outside-domain=%d\n%!" seed
        cases valid stale out;
      Alcotest.(check (list string)) "no mismatches" [] (List.filteri (fun i _ -> i < 5) failures);
      Alcotest.(check bool) "all three kinds exercised" true (valid > 0 && stale > 0 && out > 0))

let () =
  Alcotest.run "differential"
    [ ("lean-oracle", List.map test_case Subjects.all); ("by-construction", [ push_case; of_list_case ]); ("run-domain", [ run_case ]) ]
