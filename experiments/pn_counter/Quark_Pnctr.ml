module Counter : sig
  type t
  type op = Increment | Decrement
  val make: int -> t
  val read: t -> int
  val app_op: (int * op) -> t -> t
  val merge: t -> t -> t -> t
end = struct

  type t = int
  type op = Increment | Decrement

  let make x = x
  let increment st = st + 1
  let decrement st = st - 1
  let read st = st
  module MultiSet = Bag.Make(Int)

  let app_op op st = match op with
    | (_, Increment) -> increment st
    | (_, Decrement) -> decrement st

  let abstract st = MultiSet.add 1 ~mult:st MultiSet.empty

  let concretize t_set = MultiSet.occ 1 t_set

  let merge_rels lca a b diff inter union =
    let ixn = (inter (inter a b) lca) in
    let diff_a = diff a lca in
    let diff_b = diff b lca in
    union (union diff_a diff_b) ixn

  let merge lca a b =
    let lca_abs = abstract lca in
    let a_abs = abstract a in
    let b_abs = abstract b in
    let r_abs = merge_rels lca_abs a_abs b_abs MultiSet.diff MultiSet.inter MultiSet.sum in
    concretize r_abs

end
