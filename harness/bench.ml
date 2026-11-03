(** Generic optimization benchmark: times [reference], [plan], [check_invariant] and [run]
    on invariant-holding workloads across sizes.

    Method (hand-rolled, no dependencies): per (function, size) a pool of 64 distinct inputs;
    warm-up; calibrate a batch so one sample takes >= 5 ms; 21 samples; report the median
    time per call with the interquartile range, and minor-heap words allocated per call.
    The clock is [Unix.gettimeofday] (microsecond resolution, so batches are long). *)

type stat = { median_ns : float; p25_ns : float; p75_ns : float; words : float }

let pool_size = 64
let samples = 21
let min_sample_s = 0.005

let time_batch f inputs k =
  let n = Array.length inputs in
  let t0 = Unix.gettimeofday () in
  for i = 0 to k - 1 do
    ignore (Sys.opaque_identity (f inputs.(i mod n)))
  done;
  Unix.gettimeofday () -. t0

let measure f inputs =
  ignore (time_batch f inputs (4 * Array.length inputs)) (* warm-up *);
  let rec calibrate k = if time_batch f inputs k >= min_sample_s then k else calibrate (2 * k) in
  let k = calibrate 1 in
  let w0 = Gc.minor_words () in
  let ts = Array.init samples (fun _ -> time_batch f inputs k *. 1e9 /. float k) in
  let words = (Gc.minor_words () -. w0) /. float (samples * k) in
  Array.sort compare ts;
  let q p = ts.(int_of_float (p *. float (samples - 1))) in
  { median_ns = q 0.5; p25_ns = q 0.25; p75_ns = q 0.75; words }

let iqr_pct s = 100. *. (s.p75_ns -. s.p25_ns) /. s.median_ns
let show s = Printf.sprintf "%10.1f ±%4.1f%%" s.median_ns (iqr_pct s)

let run (module S : Subject.S) ~seed ~sizes =
  Printf.printf "\n### %s (invariant-holding workload, seed %d)\n\n" S.name seed;
  let floor = measure (fun x -> x) [| () |] in
  Printf.printf "Harness floor (identity function): %s ns/call\n\n" (show floor);
  Printf.printf
    "| size | reference ns | plan ns | check ns | run ns | plan speedup | run speedup | words/call ref/plan/check/run |\n";
  Printf.printf "|---:|---:|---:|---:|---:|---:|---:|---:|\n";
  List.iter
    (fun size ->
      let st = Random.State.make [| seed; size |] in
      let inputs = Array.init pool_size (fun _ -> S.workload st ~size) in
      let r = measure S.reference inputs
      and p = measure S.plan inputs
      and c = measure S.check_invariant inputs
      and u = measure S.run inputs in
      Printf.printf "| %d | %s | %s | %s | %s | %.2fx | %.2fx | %.0f/%.0f/%.0f/%.0f |\n%!" size (show r)
        (show p) (show c) (show u) (r.median_ns /. p.median_ns) (r.median_ns /. u.median_ns) r.words
        p.words c.words u.words)
    sizes
