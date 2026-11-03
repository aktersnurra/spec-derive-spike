(** Adapter: generated sorted-lookup module + input generation + oracle line format. *)
module G = Gen.Sorted_lookup_gen
open Harness

type input = G.entry list * int
type output = int option

let name = "sorted_lookup"
let max_size = 1000
let reference (s, k) = G.reference s k
let plan (s, k) = G.plan s k
let check_invariant (s, _) = G.check_invariant s
let run (s, k) = Some (G.run s k) (* never refuses: no arithmetic *)
let equal_output = Option.equal Int.equal
let show_output = function None -> "none" | Some v -> Printf.sprintf "some %d" v

let to_line (s, k) =
  String.concat " "
    (string_of_int k :: List.map (fun (e : G.entry) -> Printf.sprintf "%d:%d" e.key e.value) s)

(* Spec bounds (SortedLookup.Bounded): keys, values and the query within ±10^15. *)
let bound = 1_000_000_000_000_000

(** [size] strictly increasing keys starting near [-bound], gaps in [1, max_gap]. *)
let sorted_keys st ~size =
  let max_gap = max 1 ((2 * bound) / (size + 1)) in
  let start = Pick.int_in st (-bound) (-bound + max_gap) in
  let rec go k n acc = if n = 0 then List.rev acc else go (k + Pick.int_in st 1 max_gap) (n - 1) (k :: acc) in
  go start size []

let entries st keys = List.map (fun key -> { G.key; value = Pick.int_in st (-bound) bound }) keys

(** Break strictness: duplicate a neighbour's key, swap two adjacent entries, or shuffle keys. *)
let corrupt st s =
  let a = Array.of_list s in
  let n = Array.length a in
  (if n >= 2 then
     let i = Random.State.int st (n - 1) in
     match Random.State.int st 3 with
     | 0 -> a.(i + 1) <- { (a.(i + 1)) with G.key = a.(i).G.key }
     | 1 ->
         let t = a.(i) in
         a.(i) <- a.(i + 1);
         a.(i + 1) <- t
     | _ -> Array.iteri (fun j e -> a.(j) <- { e with G.key = Pick.int_in st (-bound) bound }) a);
  Array.to_list a

(** Query: a present key, a near miss, an out-of-range miss, or any key. *)
let query st s =
  let keys = Array.of_list (List.map (fun (e : G.entry) -> e.key) s) in
  let some_key () = keys.(Random.State.int st (Array.length keys)) in
  match Random.State.int st 4 with
  | 0 when keys <> [||] -> some_key ()
  | 1 when keys <> [||] -> let k = some_key () in if k < bound then k + 1 else k - 1
  | 2 -> if Random.State.bool st then -bound else bound
  | _ -> Pick.int_in st (-bound) bound

let gen st ~size ~valid =
  let s = entries st (sorted_keys st ~size) in
  let s = if valid then s else corrupt st s in
  (s, query st s)

(** Benchmark: sorted keys, half the queries hit a uniformly chosen key, half miss
    (a key between two present keys, so the plan's early exit is mid-list on average). *)
let workload st ~size =
  let keys = List.init size (fun i -> 2 * i) in
  let s = List.map (fun key -> { G.key; value = key }) keys in
  let k = if size = 0 then 0 else 2 * Random.State.int st size + Random.State.int st 2 in
  (s, k)
