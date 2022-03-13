module IntSet = Set.Make(Int)

module Pair: sig
  include Set.OrderedType
  val make: (Z.t * Z.t) -> t
  val unmake: t -> (Z.t * Z.t)
end = struct
  type t = (Z.t * Z.t)
  let compare a b = if a = b then 0 else (if (fst a > fst b) || ((fst a = fst b) && (snd a > snd b)) then 1 else -1)
  let make a = a
  let unmake a = a
end

module PairSet = Set.Make(Pair)

type t = (Z.t * Z.t) list
type op = Add of Z.t | Rem of Z.t

let empty = []
let is_mem x s = List.exists (fun y -> snd y = x) s
let add x s = if is_mem (snd x) s then s else x::s
let rem x s = List.filter (fun y -> snd y <> x) s

let app_op st op = match op with
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


