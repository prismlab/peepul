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

val lemma1: #n: nat -> h:history n{wellformed h} 
          -> Lemma (ensures (forall c1 c2. mem c1 h /\ mem c2 h ==> length c1 = length c2)) (decreases (size h))
let rec lemma1 h = 
  let History c s ch = h in
  match ch with
  | [] -> ()
  | x::xs -> lemma1 (History c s xs); lemma1 x

val lemma2 : #n:nat -> h:history n{wellformed h}
           -> Lemma (ensures (forall h'. L.mem h' (History?.children h) ==> wellformed h')) (decreases (size h))
let rec lemma2 (History c s ch) =
  match ch with
  | [] -> ()
  | x::xs -> assert (wellformed x); lemma2 (History c s xs)

val lemma3 : #n:nat -> h:history n{wellformed h}
          -> Lemma (ensures (forall h'. L.mem h' (History?.children h) ==> Vc.hbeq (History?.clock h) (History?.clock h'))) (decreases (size h))
let rec lemma3 (History c s ch) =
  match ch with
  | [] -> ()
  | x::xs -> assert (wellformed x); lemma3 (History c s xs); lemma3 x

val lemma4 : #n:nat -> h:history n{wellformed h}
           -> Lemma (ensures (forall c. mem c h ==> Vc.hbeq (History?.clock h) c)) (decreases (size h))
val lemma5 : #n:nat -> h:history n{wellformed h} -> c:Vc.t n{Vc.hbeq c (History?.clock h)}
           -> Lemma (requires (forall k. mem k h ==> Vc.hbeq (History?.clock h) k))
                   (ensures  (forall k. mem k h ==> Vc.hbeq c k)) (decreases (size h))
let rec lemma4 h =
  let History c s ch = h in
  match ch with
  | [] -> Vc.hbeq_reflexive c
  | x::xs ->
      lemma4 x;
      lemma4 (History c s xs);
      assert (Vc.hbeq c (History?.clock x));
      assert (forall k. mem k x ==> Vc.hbeq (History?.clock x) k);
      lemma5 x c;
      assert (forall k. mem k x ==> Vc.hbeq c k);
      ()
and lemma5 (History c' s ch) c =
  match ch with
  | [] -> ()
  | x::xs -> 
      Vc.hbeq_transitive (length c) c c' (History?.clock x);
      lemma4 x;
      lemma5 x c;
      lemma4 (History c' s xs);
      lemma5 (History c' s xs) c;
      ()

val lca_ : #n:nat 
        -> h:history n{wellformed h}
        -> a:Vc.t n 
        -> b:Vc.t n 
        -> init:Vc.t n{Vc.hbeq init a /\ Vc.hbeq init b}
        -> Tot (r:Vc.t n{Vc.hbeq r a /\ Vc.hbeq r b}) (decreases %[h])
val lca_' : #n:nat 
         -> l:list (history n){forall h. L.mem h l ==> wellformed h} 
         -> a:Vc.t n 
         -> b:Vc.t n 
         -> init:Vc.t n{Vc.hbeq init a /\ Vc.hbeq init b}
         -> Tot (r:Vc.t n{Vc.hbeq r a /\ Vc.hbeq r b}) (decreases %[l])
let rec lca_ h a b init =
  lemma2 h;
  let History clock _ ch = h in
  if Vc.hbeq init clock && Vc.hbeq clock a && Vc.hbeq clock b
  then lca_' ch a b clock
  else init
and lca_' l a b init =
  match l with
  | [] -> init 
  | x::xs -> lca_' xs a b (lca_ x a b init)

val lca : #n:nat
       -> h:history n{wellformed h}
       -> a:Vc.t n{mem a h}
       -> b:Vc.t n{mem b h}
       -> r:Vc.t n{Vc.hbeq r a /\ Vc.hbeq r b}
let lca h a b = 
  lemma4 h;
  lca_ h a b (History?.clock h)
