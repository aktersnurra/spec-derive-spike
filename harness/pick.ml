(** Boundary-biased random values for input generators. *)

(** An int in [\[lo, hi\]]: the bounds, their neighbours, and 0 are each picked often. *)
let int_in st lo hi =
  match Random.State.int st 8 with
  | 0 -> lo
  | 1 -> hi
  | 2 -> if lo <= 0 && 0 <= hi then 0 else lo
  | 3 -> min hi (lo + 1)
  | 4 -> max lo (hi - 1)
  | _ -> lo + Random.State.full_int st (hi - lo + 1)

(** A size in [\[0, max\]]: degenerate sizes (0, 1, 2) and [max] are each picked often. *)
let size st max =
  match Random.State.int st 8 with
  | 0 -> 0
  | 1 -> min 1 max
  | 2 -> min 2 max
  | 3 -> max
  | _ -> Random.State.int st (max + 1)
