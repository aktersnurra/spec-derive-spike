(* Benchmark every registered example. Times are local and noisy; see README. *)
let () =
  let seed = match Sys.getenv_opt "SEED" with Some s -> int_of_string s | None -> 1 in
  Printf.printf "OCaml %s, word size %d\n" Sys.ocaml_version Sys.word_size;
  print_endline "Cells: median ns/call ± IQR as % of median (21 samples). Speedup = reference/plan, reference/run.";
  List.iter
    (fun s -> Harness.Bench.run s ~seed ~sizes:[ 0; 1; 10; 100; 1000 ])
    Subjects.all
