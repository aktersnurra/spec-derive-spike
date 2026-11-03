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

let () =
  Alcotest.run "differential" [ ("lean-oracle", List.map test_case Subjects.all) ]
