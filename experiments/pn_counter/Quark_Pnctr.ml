type t = Z.t
type op = Add | Rem

let make x = x
let increment st = Z.add st Z.one
let decrement st = Z.sub st Z.one
let read st = st
module MultiSet = Bag.Make(Int)

let app_op st op = match op with
  | (_, Add) -> increment st
  | (_, Rem) -> decrement st

let (abstract: Z.t -> MultiSet.t) = fun st -> MultiSet.add 1 ~mult:(Z.to_int st) MultiSet.empty

let concretize t_set = Z.of_int (MultiSet.occ 1 t_set)

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

