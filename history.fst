module History

open FStar.List.Tot

module L = FStar.List.Tot

module Vc = Vector_clock

type state = nat

type history (n:nat) =
| History : clock:Vc.t n
          -> state:state
          -> children:list (history n)
          -> history n

val wellformed : #n:nat -> h:history n -> Tot bool (decreases %[h])
val wellformed' : #n:nat -> l:list (history n) -> parent_clock:Vc.t n -> Tot bool (decreases %[l])
let rec wellformed h =
  let History clock _ ch = h in
  wellformed' ch clock
and wellformed' children parent_clock =
  match children with
  | [] -> true
  | x::xs ->
     let clock = History?.clock x in
     Vc.hb parent_clock clock &&
     wellformed x &&
     wellformed' xs parent_clock
     
val mem : #n:nat -> clock:Vc.t n -> h:history n -> Tot bool (decreases %[h])
val mem' : #n:nat -> l:list (history n) -> clock:Vc.t n -> Tot bool (decreases %[l])
let rec mem clock h = 
  let History k _ ch = h in
  clock = k || mem' ch clock
and mem' l clock = 
  match l with
  | [] -> false
  | x::xs -> mem clock x || mem' xs clock


val size : #n:nat -> h:history n -> Tot nat (decreases %[h])
val size' : #n:nat -> l:list (history n) -> Tot nat (decreases %[l])
let rec size h =
  let History _ _ ch = h in
  1 + size' ch
and size' l = 
  match l with
  | [] -> 0
  | x::xs -> size x + size' xs

val lemma1 : #n:nat -> h:history n{wellformed h}
           -> Lemma (ensures (forall h'. L.mem h' (History?.children h) ==> wellformed h')) (decreases (size h))
let rec lemma1 (History c s ch) =
  match ch with
  | [] -> ()
  | x::xs -> assert (wellformed x); lemma1 (History c s xs)

val lemma2 : #n:nat -> h:history n{wellformed h}
           -> Lemma (ensures (forall c. mem c h ==> Vc.hbeq (History?.clock h) c)) (decreases (size h))
val lemma2' : #n:nat -> h:history n{wellformed h} -> c:Vc.t n{Vc.hbeq c (History?.clock h)}
           -> Lemma (requires (forall k. mem k h ==> Vc.hbeq (History?.clock h) k))
                   (ensures  (forall k. mem k h ==> Vc.hbeq c k)) (decreases (size h))
let rec lemma2 h =
  let History c s ch = h in
  match ch with
  | [] -> Vc.hbeq_reflexive c
  | x::xs ->
      lemma2 x;
      lemma2 (History c s xs);
      assert (Vc.hbeq c (History?.clock x));
      assert (forall k. mem k x ==> Vc.hbeq (History?.clock x) k);
      lemma2' x c;
      assert (forall k. mem k x ==> Vc.hbeq c k);
      ()
and lemma2' (History c' s ch) c =
  match ch with
  | [] -> ()
  | x::xs -> 
      Vc.hbeq_transitive (length c) c c' (History?.clock x);
      lemma2 x;
      lemma2' x c;
      lemma2 (History c' s xs);
      lemma2' (History c' s xs) c;
      ()

val append : #n:nat -> p:(Vc.t n -> bool) 
           -> l1:list (Vc.t n){forall e. L.mem e l1 ==> p e}
           -> l2:list (Vc.t n){forall e. L.mem e l2 ==> p e}
           -> l:list (Vc.t n){forall e. L.mem e l ==> p e}
let rec append p l1 l2 =
  match l1 with
  | [] -> l2
  | x::xs -> x::(append p xs l2)

val is_concurrent : #n:nat -> v:Vc.t n -> l:list (Vc.t n) 
                  -> r:bool{(forall c. L.mem c l ==> (v = c \/ Vc.concurrent v c)) <==> r = true}
let rec is_concurrent v l =
  match l with
  | [] -> true
  | x::xs -> (v = x || Vc.concurrent v x) && is_concurrent v xs

val cross_concurrent : #n:nat -> l:list (Vc.t n) 
                     -> r:list (Vc.t n){(forall c. L.mem c r ==> L.mem c l) /\ 
                                       (forall c1 c2. L.mem c1 r /\ L.mem c2 r ==> c1 = c2 \/ Vc.concurrent c1 c2)}
let rec cross_concurrent l1 =
  match l1 with
  | [] -> []
  | x::xs -> 
      if is_concurrent x xs then begin
        x::(cross_concurrent xs)
      end else cross_concurrent xs 

val get_latest : #n:nat -> p:(Vc.t n -> bool)
               -> l:list (Vc.t n){forall c. L.mem c l ==> p c}
               -> l':list (Vc.t n){(forall c. L.mem c l' ==> L.mem c l /\ p c)}
let get_latest p l = cross_concurrent l

val lca : #n:nat -> h:history n{wellformed h} -> a:Vc.t n{mem a h} -> b:Vc.t n{mem b h}
        -> Tot (lcalst:list (Vc.t n){(forall l. L.mem l lcalst ==> mem l h /\ Vc.hbeq l a /\ Vc.hbeq l b) /\
                                    (forall c1 c2. L.mem c1 lcalst /\ L.mem c2 lcalst ==> c1 = c2 \/ Vc.concurrent c1 c2)}) (decreases (size h))
let rec lca h a b =
  lemma2 h;
  let History c s ch = h in
  match ch with
  | [] -> [c]
  | x::xs ->
      let l1 =
        if mem a x && mem b x then
            lca x a b
        else []
      in
      let h' = History c s xs in
      let l2 =
        if mem a h' && mem b h' then
            lca h' a b
        else []
      in
      assert (forall c. L.mem c l1 ==> mem c h /\ Vc.hbeq c a /\ Vc.hbeq c b);
      assert (forall c. L.mem c l2 ==> mem c h /\ Vc.hbeq c a /\ Vc.hbeq c b);
      assert (mem c h /\ Vc.hbeq c a /\ Vc.hbeq c b);
      let l = (c::(l1@l2)) in
      let p = fun c -> mem c h && Vc.hbeq c a && Vc.hbeq c b in
      let l = c::(append p l1 l2) in
      assert (forall c. L.mem c l ==> mem c h /\ Vc.hbeq c a /\ Vc.hbeq c b);
      get_latest p l
