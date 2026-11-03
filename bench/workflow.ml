(* Whole-workflow benchmark for keeping the invariant by construction (running_sum).
   Paths, each building n entries from the same amounts:
   - push:      Running_sum_t.push (generated, O(1), no check) then total (plan, O(1))
   - reference: plain cons (no cached totals) then reference (O(n))
   - run:       cons with hand-computed cached totals (data arriving from elsewhere),
                then the per-call checked run (O(n) check + plan)
   Scenario A: build n, query once. Scenario B: query after every insert. *)
module Bench = Harness.Bench
module G = Gen.Running_sum_gen
module T = Wrapper.Running_sum_t

let push_one t x = match T.push x t with Some t' -> t' | None -> t
let cons_plain s x = { G.x; cum = 0 } :: s
let cons_cached s x = { G.x; cum = x + G.plan s } :: s

let build_once = function
  | `Push -> fun xs -> T.total (List.fold_left push_one T.empty xs)
  | `Reference -> fun xs -> G.reference (List.fold_left cons_plain [] xs)
  | `Run -> fun xs -> G.run (List.fold_left cons_cached [] xs)

let query_each = function
  | `Push -> fun xs ->
      snd (List.fold_left (fun (t, acc) x -> let t = push_one t x in (t, acc + T.total t)) (T.empty, 0) xs)
  | `Reference -> fun xs ->
      snd (List.fold_left (fun (s, acc) x -> let s = cons_plain s x in (s, acc + G.reference s)) ([], 0) xs)
  | `Run -> fun xs ->
      snd (List.fold_left (fun (s, acc) x -> let s = cons_cached s x in (s, acc + G.run s)) ([], 0) xs)

let x_bound = 1_000_000_000_000

let table title sizes mk =
  Printf.printf "\n#### %s\n\n" title;
  Printf.printf "| n | push path ns | reference ns | checked run ns | push speedup | run speedup |\n";
  Printf.printf "|---:|---:|---:|---:|---:|---:|\n";
  List.iter
    (fun n ->
      let st = Random.State.make [| 3; n |] in
      let inputs =
        Array.init Bench.pool_size (fun _ ->
            List.init n (fun _ -> Random.State.full_int st (2 * x_bound + 1) - x_bound))
      in
      let p = Bench.measure (mk `Push) inputs
      and r = Bench.measure (mk `Reference) inputs
      and u = Bench.measure (mk `Run) inputs in
      Printf.printf "| %d | %s | %s | %s | %.2fx | %.2fx |\n%!" n (Bench.show p) (Bench.show r)
        (Bench.show u) (r.median_ns /. p.median_ns) (r.median_ns /. u.median_ns))
    sizes

let per_op sizes =
  Printf.printf "\n#### Per-insert cost (build only, n inserts; ns and minor words per insert)\n\n";
  Printf.printf "| n | push ns/op | push words/op | plain cons ns/op | plain cons words/op |\n";
  Printf.printf "|---:|---:|---:|---:|---:|\n";
  List.iter
    (fun n ->
      let st = Random.State.make [| 5; n |] in
      let inputs =
        Array.init Bench.pool_size (fun _ ->
            List.init n (fun _ -> Random.State.full_int st (2 * x_bound + 1) - x_bound))
      in
      let p = Bench.measure (fun xs -> List.fold_left push_one T.empty xs) inputs
      and c = Bench.measure (fun xs -> List.fold_left cons_plain [] xs) inputs in
      let f = float n in
      Printf.printf "| %d | %.2f | %.1f | %.2f | %.1f |\n%!" n (p.median_ns /. f) (p.words /. f)
        (c.median_ns /. f) (c.words /. f))
    sizes

let run () =
  Printf.printf "\n### running_sum: keeping the invariant by construction (whole workflow)\n";
  Printf.printf "\nHarness floor (identity function): %s ns/call\n" (Bench.show (Bench.measure (fun x -> x) [| () |]));
  let sizes = [ 1; 10; 100; 1000 ] in
  table "A. Build n entries, then query the total once" sizes build_once;
  table "B. Query the total after every insert (n inserts, n queries)" sizes query_each;
  per_op [ 10; 100; 1000 ]
