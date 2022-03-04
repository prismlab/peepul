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

  let app_op op st = match op with
    | Increment -> increment st
    | Decrement -> decrement st

  let merge lca a b = a + b - lca

end
