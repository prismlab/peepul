module Queue: sig
  type t
  type op = Enqueue of int | Dequeue
  val empty : t
  val peek : t -> int option
  val app_op: (int * op) -> t -> t
  val merge : t -> t -> t -> t
end = struct

  type t = (int * int) list * (int * int) list
  type op = Enqueue of int | Dequeue

  let empty = ([], [])
  let norm q = match q with
    | [], l -> (List.rev l, [])
    | _ -> q
  let to_list (front, back) = front @ (List.rev back)

  let enqueue (front, back) a = (front, a::back)

  let dequeue q = match q with
    | [], [] -> (None, ([], []))
    | [], x::xs -> let (l1, l2) = norm q in
      (Some (List.hd l1), ((List.tl l1), l2))
    | x::xs, l -> (Some x, (xs, l))

  let app_op op st = match op with
    | (id, Enqueue x) -> enqueue st (id, x)
    | (_, Dequeue) -> snd (dequeue st)

  let peek q = match q with
    | [], [] -> None
    | [], x::xs -> Some (fst (List.hd (fst (norm q))))
    | x::xs, _ -> Some (fst x)

  module PairSet = Set.Make(struct
      type t = (int * int)
      let compare a b = if a = b then 0 else (if a < b then 1 else -1) end)

  module PairPairSet = Set.Make(struct
      type t = ((int * int) * (int * int))
      let compare a b = if a = b then 0 else (if a < b then 1 else -1) end)

  let r_mem q =
    let q_list = to_list q in
    List.fold_left (fun acc x -> PairSet.union (PairSet.singleton x) acc) PairSet.empty q_list

  let r_cross x xs =
    let acc_list = PairSet.elements xs in
    List.fold_left (fun acc a -> PairPairSet.union acc (PairPairSet.singleton (x, a))) PairPairSet.empty acc_list

  let rec r_cross_sets s1 s2 =
    let s1_list = PairSet.elements s1 in
    List.fold_left (fun acc x -> PairPairSet.union acc (r_cross x s2)) PairPairSet.empty s1_list

  let rec r_ob q = match (to_list q) with
    | [] -> PairPairSet.empty
    | x::xs -> PairPairSet.union (r_cross x (r_mem (xs, []))) (r_ob (xs, []))

  let abstract q = (r_mem q, r_ob q)

  let merge_rels lca a b diff inter union =
    let ixn = (inter (inter a b) lca) in
    let diff_a = diff a lca in
    let diff_b = diff b lca in
    union (union diff_a diff_b) ixn

  let merge_r lca a b =
    let (lca_mem, lca_ob) = abstract lca in
    let (a_mem, a_ob) = abstract a in
    let (b_mem, b_ob) = abstract b in
    let res_mem = merge_rels lca_mem a_mem b_mem PairSet.diff PairSet.inter PairSet.union in
    let res_ob_h = merge_rels lca_ob a_ob b_ob PairPairSet.diff PairPairSet.inter PairPairSet.union in
    let res_ob = PairPairSet.inter res_ob_h (r_cross_sets res_mem res_mem) in
    (res_mem, res_ob)

  let sort_pair a b =  if a < b then (a, b) else (b, a)

  exception CyclicGraph: (int * int) list -> exn

  let dfs graph visited start =
    let rec explore path visited node =
      if List.mem node path then (Printf.printf "Cycle found!\n";
                                  List.iter (fun x -> Printf.printf "(%d, %d) -> " (fst x) (snd x)) path;
                                  raise (CyclicGraph path)) else
      if List.mem node visited then visited else
        let new_path = (path @ [node]) in
        let edges = List.assoc node graph in
        let visited = List.fold_left (fun visited node -> explore new_path visited node) visited edges in
        (visited @ [node])
    in explore [] visited start

  let topological_sort adj_list =
    List.fold_left (fun visited (node, _) -> dfs adj_list visited node) [] adj_list

  let to_adj_list (vertices, edges) =
    PairSet.fold
      (fun x acc -> acc @ [(x, PairSet.elements (PairSet.filter (fun y -> x <> y && PairPairSet.mem (x, y) edges) vertices))]) vertices []

  let concretize (r_mem, r_ob) =
    if r_ob = PairPairSet.empty then (PairSet.elements r_mem, []) else
      let ord_ob = PairSet.fold (fun x acc ->
          PairSet.fold (fun y acc0 -> if (PairPairSet.mem (x, y) acc0 || PairPairSet.mem (y, x) acc0) then acc0
                         else PairPairSet.add (sort_pair x y) acc0) (PairSet.filter (fun a -> a <> x) r_mem) acc) r_mem r_ob in
      let adj_list = to_adj_list (r_mem, ord_ob) in
      let front = topological_sort adj_list in
      (List.rev front, [])

  let merge lca a b = concretize (merge_r lca a b)

end

