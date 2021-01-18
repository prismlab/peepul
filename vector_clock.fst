module Vector_clock

open FStar.List.Tot

type t (n:nat) = lst:list nat{n > 0 && length lst = n}

val tl : #n:nat{n > 1} -> t n -> t (n-1)
let tl (x::xs) = xs

type ordering =
| Happened_before
| Happened_after
| Concurrent
| Equal

val compare : v1:list nat -> v2:list nat{length v1 = length v2} -> ordering
let rec compare v1 v2 =
  match v1, v2 with
  | [], [] -> Equal
  | x::xs, y::ys -> 
      if x = y then compare xs ys
      else if x < y then 
        match compare xs ys with
        | Equal | Happened_before -> Happened_before
        | _ -> Concurrent
      else match compare xs ys with
           | Equal | Happened_after -> Happened_after
           | _ -> Concurrent

val hb: #n:nat -> v1:t n -> v2:t n -> bool
let hb a b = compare a b = Happened_before

val hbeq: #n:nat -> v1:t n -> v2:t n -> bool
let hbeq a b =
  match compare a b with
  | Happened_before | Equal -> true
  | _ -> false

val lemma1 : v:list nat -> Lemma (ensures (compare v v = Equal))
let rec lemma1 v = 
  match v with
  | [] -> ()
  | x::xs -> lemma1 xs

val hbeq_reflexive : #n:nat -> v:t n -> Lemma (ensures (hbeq v v))
let hbeq_reflexive v = lemma1 v

val lemma2 : v1:list nat -> v2:list nat{length v1 = length v2} 
          -> Lemma (ensures (compare v1 v2 = Equal ==> v1 = v2))
let rec lemma2 v1 v2 = 
  match v1, v2 with
  | [], [] -> ()
  | x::xs, y::ys ->
      if x = y then lemma2 xs ys
      else ()

val hbeq_transitive : n:nat -> v1:t n -> v2:t n{hbeq v1 v2} -> v3:t n{hbeq v2 v3}
                    -> Lemma (ensures (hbeq v1 v3))
let rec hbeq_transitive n v1 v2 v3 =
   match compare v1 v2 with
   | Equal -> lemma2 v1 v2
   | Happened_before ->
       match v1, v2, v3 with
       | x::[], y::[], z::[] -> ()
       | x::xs, y::ys, z::zs -> hbeq_transitive (n - 1) xs ys zs
