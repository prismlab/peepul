module P = Peepul_Orset_opt
module Q = Quark_Orset

let range = 1000
let insert_ratio = 90

let _ = Random.self_init ()

let r = ref 0
let next_id () =
  let v = !r in
  incr r;
  Z.of_int v

let random x = Z.of_int (Random.int x)

let random_ops r =
  let (id, ele) = (next_id (), random range) in
  if (Random.int 100 < r) then ((id, P.Add ele), (id, Q.Add ele))
  else ((id, P.Rem ele), (id, Q.Rem ele))

let pick_r r r1 r2 = if (Random.int 100 < r) then r1 else r2

let app_op (p_set, q_set) (p_op, q_op) = (P.app_op p_set p_op), (Q.app_op q_set q_op)


let peepul_merge lca a b = P.merge1 lca a b

let quark_merge lca a b = Q.merge lca a b

let rec gen_lca p q count =
  if count = 0 then (p, q) else
    let (p, q) = app_op (p, q) (random_ops insert_ratio) in
    gen_lca p q (count - 1)

let rec test_h a b count =
  if count = 0 then (a, b) else
    let replica_ratio = 50 in
    let (p_a, q_a), (p_b, q_b) = if pick_r replica_ratio "a" "b" = "a" then
        ((app_op a (random_ops insert_ratio)), b) else (a, (app_op b (random_ops insert_ratio))) in
    test_h (p_a, q_a) (p_b, q_b) (count - 1)

let test lca_ops ops =
  let (p_l, q_l) = gen_lca [] [] lca_ops in
  Printf.printf "p_l=%d q_l=%d\n%!" (List.length p_l) (List.length q_l);
  let ((p_a, q_a), (p_b, q_b)) = test_h (p_l, q_l) (p_l, q_l) ops in
  Gc.full_major();
  let p_start = Unix.gettimeofday() in
  let p_merge = peepul_merge p_l p_a p_b in
  let p_end = Unix.gettimeofday () in
  Gc.full_major();
  let q_start = Unix.gettimeofday() in
  let q_merge = quark_merge q_l q_a q_b in
  let q_end = Unix.gettimeofday () in
  Printf.printf "Peepul merge - %fs \nQuark merge - %fs\n" (p_end -. p_start) (q_end -. q_start)

let run =
  let lca_ops = try int_of_string Sys.argv.(1) with _ -> 50000 in
  let merge_ops = 1000 in
  test lca_ops merge_ops
