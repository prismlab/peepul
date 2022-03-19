
module M = Peepul_Orset_opt_detailed

let _ = Random.self_init ()

let random x = Z.of_int (Random.int x)

let max_size = ref 0

let size l = List.length l

let l_random l = if l = [] then (Z.of_int (-1), []) else let ele = List.nth l (Random.int (List.length l)) in
    (ele, List.filter (fun x -> x <> ele) l)

let g_random l = if l = [] then Z.of_int (-1) else List.nth l (Random.int (List.length l))

let add_random x l = if List.mem x l then (x, l) else (x, x::l)

let rec random_ops r1 r2 r_l = let r = Random.int 100 in
  if (r < r1) then
    begin
      if r_l = [] then (random_ops (-1) 101 r_l) else
      (let ele = (g_random r_l) in ((ele, M.Look, ele), r_l))
    end
  else
    begin
      if (r >= r1 && r < r2) then
        begin
          let (ele, l) = add_random (random 1000) r_l in
          ((random 1000000, M.Add, ele), l)
        end
      else
        begin
          let (ele, l) = (l_random r_l) in
          ((random 1000000, M.Rem, ele), l)
        end
    end

let pick_r r r1 r2 = if (Random.int 100 < r) then r1 else r2

let app_op set (op, l) =
  let res = (M.app_op set op) in
  max_size := max (size res) (!max_size);
  (res, l)

let merge lca a b =
  let res = M.merge_s lca a b in
  max_size := max (size res) (!max_size);
  res

let rec test lca a b a_l b_l count =
  if count = 0 then () else
  let lca = merge lca a b in
  let replica_ratio = 50 in
  let insert_ratio = 50 in
  let merge_ratio = 500 in
  let ((a, a_l), (b, b_l)) = if pick_r replica_ratio a b = a then (app_op a (random_ops 60 90 a_l), (b, b_l))
    else ((a, a_l), app_op b (random_ops 60 90 b_l)) in
  let lca = if (count mod merge_ratio = 0) then merge lca a b else (lca) in
  test lca a b a_l b_l (count-1)

let rec gen_lca p p_l count =
  if count = 0 then (p, p_l) else
    let insert_ratio = 70 in
    let (p, p_l) = app_op p (random_ops 60 90 p_l) in
    gen_lca p p_l (count - 1)

let _ =
  let (lca, lca_l) = gen_lca [] [] 1000 in
  let a = lca in
  let b = lca in
  let t = test lca a b lca_l lca_l 1000 in
  Printf.printf "Max size - %d\n" (!max_size)

