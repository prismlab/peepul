module Queue: sig
  type queue = int list * int list
  type op = Enqueue of int | Dequeue
  val enqueue: queue -> int -> queue
  val dequeue: queue -> int option * queue
  val app_op: op -> queue -> queue
end = struct

type queue = int list * int list
type op = Enqueue of int | Dequeue

let norm q = match q with
  | [], l -> (List.rev l, [])
  | _ -> q

let enqueue q a = match q with
  | l, l1 -> a::l, l1

let dequeue q = match q with
  | [], [] -> (None, ([], []))
  | [], x::xs -> let (l1, l2) = norm q in
    (Some (List.hd l1), ((List.tl l1), l2))
  | x::xs, l -> (Some x, (xs, l))

let app_op op st = match op with
  | Enqueue x -> enqueue st x
  | Dequeue -> snd (dequeue st)

end

