module Counter : sig
  type t = int * int
  type op = Increment | Decrement
  val increment: t -> t
  val decrement: t -> t
  val read: t -> int
  val app_op: op -> t -> t
  val merge: t -> t -> t -> t
end = struct

type t = int * int
type op = Increment | Decrement

let increment (i, d) = (i + 1, d)
let decrement (i, d) = (i, d + 1)
let read (i, d) = i - d

let app_op op st = match op with
  | Increment -> increment st
  | Decrement -> decrement st

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

let abstract st = PairSet.add (Pair.make (2, snd st)) (PairSet.singleton (Pair.make (1, fst st)))

let concrete r_pair =
  let fst_r = PairSet.get_idx r_pair 1 in
  let snd_r = PairSet.get_idx r_pair 2 in
  (fst_r, snd_r)

let merge_c lca a b = a + b - lca

let merge_r lca a b =
  PairSet.map (fun x -> Pair.make (Pair.fst x, merge_c (Pair.snd x) (PairSet.get_idx a (Pair.fst x)) (PairSet.get_idx b (Pair.fst x)))) lca

let merge lca a b =
  let lca_r = abstract lca in
  let a_r = abstract a in
  let b_r = abstract b in
  let res_r = merge_r lca_r a_r b_r in
  concrete res_r

end
