module Vector_clock

open FStar.List.Tot

type t (n:nat) = lst:list nat{n > 0 && length lst = n}

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

val compare : #n:nat -> v1:t n -> v2:t n -> ordering
let compare v1 v2 = compare' v1 v2 Equal

val hb: #n:nat -> v1:t n -> v2:t n -> bool
let hb a b = compare a b = Happened_before

val hbeq: #n:nat -> v1:t n -> v2:t n -> bool
let hbeq a b =
  match compare a b with
  | Happened_before | Equal -> true
  | _ -> false

val lemma1 : v:list nat -> Lemma (ensures (compare' v v Equal = Equal)) 
let rec lemma1 v =
  match v with
  | [] -> ()
  | x::xs -> lemma1 xs

val hbeq_reflexive : #n:nat -> v:t n -> Lemma (ensures (hbeq v v))
let hbeq_reflexive v = lemma1 v

val lemma2 : v1:list nat -> v2:list nat{length v1 = length v2} -> o:ordering{not (o = Equal)}
           -> Lemma (ensures (not (compare' v1 v2 o = Equal)))
let rec lemma2 v1 v2 o =
  match v1, v2, o with
  | [], [], _ -> ()
  | _, _, Concurrent -> ()
  | x::xs, y::ys, Happened_before -> 
     if x > y then ()
     else lemma2 xs ys Happened_before
  | x::xs, y::ys, Happened_after -> 
     if x < y then ()
     else lemma2 xs ys Happened_after

val lemma3 : v1:list nat -> v2:list nat{length v1 = length v2} -> o:ordering 
           -> Lemma (ensures (compare' v1 v2 o = Equal ==> v1 = v2))
let rec lemma3 v1 v2 o =
  match v1, v2, o with
  | [], [], _ -> ()
  | x::xs, y::ys, Equal -> 
      if x = y then lemma3 xs ys Equal
      else if x < y then lemma2 xs ys Happened_before
      else lemma2 xs ys Happened_after
  | x::xs, y::ys, Happened_before ->
      if x > y then ()
      else lemma2 xs ys Happened_before
  | x::xs, y::ys, Happened_after ->
      if x < y then ()
      else lemma2 xs ys Happened_after
  | _, _, Concurrent -> ()

val hbeq_precede : #n:nat -> v1:t n -> v2:t n{hbeq v1 v2}
                 -> Lemma (ensures (forall v3. hbeq v2 v3 ==> hbeq v1 v3))
let hbeq_precede v1 v2 =
  match compare v1 v2 with
  | Equal -> lemma3 v1 v2 Equal
  | Happened_before -> admit ()
  
val hbeq_transitive : #n:nat -> v1:t n -> v2:t n{hbeq v1 v2} -> v3:t n{hbeq v2 v3} -> Lemma (ensures (hbeq v1 v3))
let hbeq_transitive v1 v2 v3 =
  match compare v1 v2 with
  | Equal -> lemma3 v1 v2 Equal
  | Happened_before -> 
     begin match compare v2 v3 with
     | Equal -> lemma3 v2 v3 Equal
     | Happened_before -> admit ()
     end
