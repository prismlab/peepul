
open Fqueue

let _ = Random.self_init ()

let random x = Z.of_int (Random.int x)

let pick_r r r1 r2 = if (Random.int 100 < r) then r1 else r2

let app_op queue r = if (Random.int 100 < r) then (enqueue (random 1000000, random 10000) queue) else
    (snd (dequeue queue))

let merge lca a b = S ((merge_s (tolist lca) (tolist a) (tolist b)), [])

let rec test lca a b count =
  if count = 0 then () else
  let lca = merge lca a b in
  let replica_ratio = 50 in
  let insert_ratio = 50 in
  let merge_ratio = 500 in
  let (a, b) = if pick_r replica_ratio a b = a then (app_op a insert_ratio, b) else (a, app_op b insert_ratio) in
  let lca = if (count mod merge_ratio = 0) then merge lca a b else lca in
  test lca a b (count-1)

let rec gen_list acc x =
  if x = 0 then acc else
    gen_list ((random 100000, random 1000)::acc) (x-1)

let _ =
  let lca = S (gen_list [] 50, gen_list [] 50) in
  let a = S (gen_list [] 60, gen_list [] 60) in
  let b = S (gen_list [] 60, gen_list [] 60) in
  test lca a b 10000


