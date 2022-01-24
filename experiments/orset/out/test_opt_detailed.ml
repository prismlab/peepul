let _ = Random.self_init ()

let random x = Z.of_int (Random.int x)

let random_ops r = if (Random.int 100 < r) then (random 1000000, Orset_opt_detailed.Add, (random 25))
  else (random 1000000, Orset_opt_detailed.Rem, (random 25))

let pick_r r r1 r2 = if (Random.int 100 < r) then r1 else r2

let app_op set op = (Orset_opt_detailed.app_op set op)

let merge lca a b = Orset_opt_detailed.merge_s lca a b

let rec test lca a b count =
  if count = 0 then () else
  let lca = merge lca a b in
  let replica_ratio = 50 in
  let insert_ratio = 50 in
  let merge_ratio = 500 in
  let (a, b) = if pick_r replica_ratio a b = a then (app_op a (random_ops insert_ratio), b) else (a, app_op b (random_ops insert_ratio)) in
  let lca = if (count mod merge_ratio = 0) then merge lca a b else lca in
  test lca a b (count-1)

let rec gen_list acc x =
  if x = 0 then acc else
    gen_list ((random 100000, random 1000)::acc) (x-1)

let _ =
  Memtrace.trace_if_requested ();
  let lca = gen_list [] 10000 in
  let a = lca in
  let b = lca in
  test lca a b 10000


