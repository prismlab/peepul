module Vector_clock

open FStar.List.Tot

type t = v:list nat{Cons? v}

type ordering = 
| Happened_before 
| Happened_after
| Concurrent
| Equal

val compare' : v1:list nat -> v2:list nat{length v2 = length v1} -> ordering -> ordering
let rec compare' v1 v2 r = 
    match v1, v2, r with
    | [], [], _ -> r
    | x::xs, y::ys, Equal -> 
        if x = y then compare' xs ys Equal
        else if x < y then compare' xs ys Happened_before
        else compare' xs ys Happened_after
    | x::xs, y::ys, Happened_before -> 
        if x > y then Concurrent
        else compare' xs ys Happened_before
    | x::xs, y::ys, Happened_after -> 
        if x < y then Concurrent
        else compare' xs ys Happened_after
    | x::xs, y::ys, Concurrent -> Concurrent

val compare : v1:t -> v2:t{length v2 = length v1} -> ordering
let compare v1 v2 = compare' v1 v2 Equal

val hb: v1:t -> v2:t{length v1 = length v2} -> bool
let hb a b = compare a b = Happened_before
