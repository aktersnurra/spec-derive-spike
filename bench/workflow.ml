(* Whole-workflow benchmark for keeping the invariant by construction (running_sum).
   Paths, each consuming the same n amounts:
   - reference:    plain cons (no cached totals), then reference (O(n) per query)
   - generated:    Running_sum_t.push (generated, proved; O(1)) then total (plan, O(1))
   - hand:         hand-written { total; items } with push/total, no checks
   - hand+checks:  the same with the generated push's bounds checks and Option result
   Scenario A: build n, query once. Scenario B: query after every insert. *)
module Bench = Harness.Bench
module G = Gen.Running_sum_gen
module T = Wrapper.Running_sum_t
module P = Baseline.Plain
module C = Baseline.Checked

let gen_push t x = match T.push x t with Some t' -> t' | None -> t
let chk_push t x = match C.push x t with Some t' -> t' | None -> t
let hand_push t x = P.push x t
let cons_plain s x = { G.x; cum = 0 } :: s

type path = { name : string; once : int list -> int; each : int list -> int; build : int list -> Obj.t }

let path name empty push query =
  {
    name;
    once = (fun xs -> query (List.fold_left push empty xs));
    each = (fun xs -> snd (List.fold_left (fun (t, acc) x -> let t = push t x in (t, acc + query t)) (empty, 0) xs));
    build = (fun xs -> Obj.repr (List.fold_left push empty xs));
  }

let paths =
  [ path "reference" [] cons_plain G.reference; path "generated" T.empty gen_push T.total;
    path "hand" P.empty hand_push P.total; path "hand+checks" C.empty chk_push C.total ]

let x_bound = 1_000_000_000_000

let inputs ~seed n =
  let st = Random.State.make [| seed; n |] in
  Array.init Bench.pool_size (fun _ ->
      List.init n (fun _ -> Random.State.full_int st (2 * x_bound + 1) - x_bound))

let table title sizes pick =
  Printf.printf "\n#### %s\n\n| n |" title;
  List.iter (fun p -> Printf.printf " %s ns |" p.name) paths;
  Printf.printf " generated / hand+checks |\n|---:|";
  List.iter (fun _ -> Printf.printf "---:|") paths;
  Printf.printf "---:|\n";
  List.iter
    (fun n ->
      let inp = inputs ~seed:3 n in
      let stats = List.map (fun p -> Bench.measure (pick p) inp) paths in
      Printf.printf "| %d |" n;
      List.iter (fun s -> Printf.printf " %s |" (Bench.show s)) stats;
      let g = List.nth stats 1 and c = List.nth stats 3 in
      Printf.printf " %.2fx |\n%!" (g.median_ns /. c.median_ns))
    sizes

let per_op sizes =
  Printf.printf "\n#### Per-insert cost (build only; ns and minor words per insert)\n\n| n |";
  List.iter (fun p -> Printf.printf " %s ns | words |" p.name) paths;
  Printf.printf "\n|---:|";
  List.iter (fun _ -> Printf.printf "---:|---:|") paths;
  Printf.printf "\n";
  List.iter
    (fun n ->
      let inp = inputs ~seed:5 n in
      let f = float n in
      Printf.printf "| %d |" n;
      List.iter
        (fun p ->
          let s = Bench.measure p.build inp in
          Printf.printf " %.2f | %.1f |" (s.median_ns /. f) (s.words /. f))
        paths;
      Printf.printf "\n%!")
    sizes

let run () =
  Printf.printf "\n### running_sum: keeping the invariant by construction (whole workflow)\n";
  Printf.printf "\nHarness floor (identity function): %s ns/call\n"
    (Bench.show (Bench.measure (fun x -> x) [| () |]));
  let sizes = [ 10; 100; 1000 ] in
  table "A. Build n entries, then query the total once" sizes (fun p -> p.once);
  table "B. Query the total after every insert (n inserts, n queries)" sizes (fun p -> p.each);
  per_op sizes
