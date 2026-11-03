module G = Gen.Running_sum_gen

type t = G.entry list

let empty = []
let of_list s = if G.check_invariant s then Some s else None
let push = G.push
let total = G.plan
