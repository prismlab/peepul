
let _ = Random.self_init ()

let random_ops r = if (Random.int 100 < r) then (Random.int 1000000, Orset_opt_detailed.Add, Random.int 10000)
  else (Random.int 1000000, Orset_opt_detailed.Rem, Random.int 10000)

let pick_r r r1 r2 = if (Random.int 100 < r) then r1 else r2

let app_op set op = (Orset_opt_detailed.app_op set op)

let merge lca a b = Orset_opt_detailed.merge_s lca a b

let rec test lca a b count =
  if count = 0 then () else
  let lca = merge lca a b in
  let replica_ratio = 50 in
  let insert_ratio = 80 in
  let merge_ratio = 5 in
  let (a, b) = if pick_r replica_ratio a b = a then (app_op a (random_ops insert_ratio), b) else (a, app_op b (random_ops insert_ratio)) in
  let lca = if (count mod 100 < merge_ratio) then merge lca a b else lca in
  test lca a b (count-1)

let _ =
  test [] [] [] 10000


