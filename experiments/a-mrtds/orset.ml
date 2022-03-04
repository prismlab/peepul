module Orset : sig
  type t
  type op = Add of int | Rem of int
  val empty : t
  val is_mem : int -> t -> bool
  val app_op : op -> t -> t
  val merge : t -> t -> t -> t
end = struct
  module IntSet = Set.Make(Int)

  type t = IntSet.t
  type op = Add of int | Rem of int

  let empty = IntSet.empty
  let is_mem = IntSet.mem
  let add = IntSet.add
  let rem = IntSet.remove

  let app_op op st = match op with
    | Add x -> add x st
    | Rem x -> rem x st

  let merge lca a b =
    let ixn = (IntSet.inter (IntSet.inter a b) lca) in
    let diff_a = IntSet.diff a lca in
    let diff_b = IntSet.diff b lca in
    IntSet.union (IntSet.union diff_a diff_b) ixn

end


