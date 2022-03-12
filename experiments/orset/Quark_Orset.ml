module Orset : sig
  type t
  type op = Add of int | Rem of int
  val empty : t
  val is_mem : int -> t -> bool
  val app_op : (int * op) -> t -> t
  val merge : t -> t -> t -> t
end = struct
  module IntSet = Set.Make(Int)

  module Pair: sig
    include Set.OrderedType
    val make: (int * int) -> t
    val unmake: t -> (int * int)
  end = struct
    type t = (int * int)
    let compare a b = if a = b then 0 else (if (fst a > fst b) || ((fst a = fst b) && (snd a > snd b)) then 1 else -1)
    let make a = a
    let unmake a = a
  end

  module PairSet = Set.Make(Pair)

  type t = (int * int) list
  type op = Add of int | Rem of int

  let empty = []
  let is_mem x s = List.exists (fun y -> snd y = x) s
  let add x s = if is_mem (snd x) s then s else x::s
  let rem x s = List.filter (fun y -> snd y <> x) s

  let app_op op st = match op with
    | (id, Add x) -> add (id, x) st
    | (_, Rem x) -> rem x st

  let abstract st = List.fold_left (fun acc x -> PairSet.add (Pair.make x) acc) PairSet.empty st

  let concretize m_set = PairSet.fold (fun x acc -> (Pair.unmake x)::acc) m_set []

  let merge_r lca a b =
    let ixn = (PairSet.inter (PairSet.inter a b) lca) in
    let diff_a = PairSet.diff a lca in
    let diff_b = PairSet.diff b lca in
    PairSet.union (PairSet.union diff_a diff_b) ixn

  let merge lca a b =
    let lca_abs = abstract lca in
    let a_abs = abstract a in
    let b_abs = abstract b in
    let r_abs = merge_r lca_abs a_abs b_abs in
    concretize r_abs

end


