module Queue: sig
  type t
  type op = Enqueue of int | Dequeue
  val empty : t
  val peek : t -> int option
  val app_op: op -> t -> t
  (* val merge : t -> t -> t -> t *)
end = struct

  type t = int list * int list
  type op = Enqueue of int | Dequeue

  let empty = ([], [])
  let norm q = match q with
    | [], l -> (List.rev l, [])
    | _ -> q
  let to_list (front, back) = front @ (List.rev back)

  let enqueue (front, back) a = (a::front, back)

  let dequeue q = match q with
    | [], [] -> (None, ([], []))
    | [], x::xs -> let (l1, l2) = norm q in
      (Some (List.hd l1), ((List.tl l1), l2))
    | x::xs, l -> (Some x, (xs, l))

  let app_op op st = match op with
    | Enqueue x -> enqueue st x
    | Dequeue -> snd (dequeue st)

  let peek q = match q with
    | [], [] -> None
    | [], x::xs -> Some (List.hd (fst (norm q)))
    | x::xs, _ -> Some x

  module IntSet = Set.Make(Int)

  module Pair: sig include Set.OrderedType;; val make: (int * int) -> t;; val fst: t -> int;; val snd: t -> int  end = struct
    type t = (int * int)
    let compare a b = if a = b then 0 else (if (fst a > fst b) || ((fst a = fst b) && (snd a > snd b)) then 1 else -1)
    let make a = a
    let fst = fst
    let snd  = snd
  end
  module PairSet = struct
    include Set.Make(Pair)
    let get_idx set i = Pair.snd (List.hd (elements (filter (fun x -> Pair.fst x = i) set)))
  end

  let r_mem q =
    let q_list = to_list q in
    List.fold_left (fun acc x -> IntSet.union (IntSet.singleton x) acc) IntSet.empty q_list

  let r_cross x acc =
    let acc_list = IntSet.elements acc in
    List.fold_left (fun acc a -> PairSet.union acc (PairSet.singleton (Pair.make (x, a)))) PairSet.empty acc_list

  let rec r_cross_sets s1 s2 =
    let s1_list = IntSet.elements s1 in
    match s1_list with
    | [] -> PairSet.empty
    | x::xs -> r_cross x s2

  let r_ob q =
    let rec r_ob_h set q_l = match q_l with
      | [] -> PairSet.empty
      | x::xs -> PairSet.union set (r_cross x (r_mem (xs, []))) in
    r_ob_h PairSet.empty (to_list q)

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
    let res_mem = merge_rels lca_mem a_mem b_mem IntSet.diff IntSet.inter IntSet.union in
    let res_ob_h = merge_rels lca_ob a_ob b_ob PairSet.diff PairSet.inter PairSet.union in
    let res_ob = PairSet.inter res_ob_h (r_cross_sets res_mem res_mem) in
    (res_mem, res_ob)

end

