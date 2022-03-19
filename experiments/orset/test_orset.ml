
module M = Peepul_Orset_opt

let _ = Random.self_init ()

let random x = Z.of_int (Random.int x)

let l_random l = if l = [] then (Z.of_int (-1), []) else let ele = List.nth l (Random.int (List.length l)) in
  (ele, List.filter (fun x -> x <> ele) l)

let add_random x l = if List.mem x l then (x, l) else (x, x::l)

let random_ops r r_l = if (Random.int 100 < r) then
    begin
      let (ele, l) = add_random (random 1000) r_l in
      ((random 1000000, M.Add ele), l)
    end
  else
    begin
      let (ele, l) = (l_random r_l) in
        ((random 1000000, M.Rem ele), l)
    end

let pick_r r r1 r2 = if (Random.int 100 < r) then r1 else r2

let app_op set (op, l) =
  let p_start = Unix.gettimeofday() in
  let res = (M.app_op set op) in
  let p_end = Unix.gettimeofday() in
  (res, l, p_end -. p_start)

let merge lca a b =
  let p_start = Unix.gettimeofday() in
  let res = M.merge1 lca a b in
  let p_end = Unix.gettimeofday() in
  (res, p_end -. p_start)

let rec test lca a b a_l b_l time count =
  if count = 0 then time else
  let (lca, t_l) = merge lca a b in
  let replica_ratio = 50 in
  let insert_ratio = 50 in
  let merge_ratio = 500 in
  let ((a, a_l, t_a), (b, b_l, t_b)) = if pick_r replica_ratio a b = a then (app_op a (random_ops insert_ratio a_l), (b, b_l, 0.0))
    else ((a, a_l, 0.0), app_op b (random_ops insert_ratio b_l)) in
  let (lca, t_la) = if (count mod merge_ratio = 0) then merge lca a b else (lca, 0.0) in
  test lca a b a_l b_l (time +. t_a +. t_b +. t_l +. t_la) (count-1)

let rec gen_lca p p_l count =
  if count = 0 then (p, p_l) else
    let insert_ratio = 70 in
    let (p, p_l, t_p) = app_op p (random_ops insert_ratio p_l) in
    gen_lca p p_l (count - 1)

let _ =
  Memtrace.trace_if_requested ();
  let s = read_int () in
  let p_start = Unix.gettimeofday() in
  let (lca, lca_l) = gen_lca [] [] s in
  let p_end = Unix.gettimeofday () in
  let a = lca in
  let b = lca in
  let t = test lca a b lca_l lca_l 0.0 1000 in
  Printf.printf "Total time - %fs\n" ((p_end -. p_start) +. t)

