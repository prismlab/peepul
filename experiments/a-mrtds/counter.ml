module Counter : sig
  type t
  type op = Increment | Decrement
  val make: int -> t
  val read: t -> int
  val app_op: op -> t -> t
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
    | Increment -> increment st
    | Decrement -> decrement st

  let abstract t =
    let rec abs_help ctr set = if ctr = 0 then set else abs_help (ctr-1) (MultiSet.add 1 set) in
    abs_help t MultiSet.empty

  let concrete t_set = MultiSet.occ 1 t_set

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
    concrete r_abs

  let _ = Printf.printf "%d\n" (merge 1 2 3)

end
