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
           -> Lemma (ensures (forall c. mem c h ==> Vc.hbeq (History?.clock h) c))
let rec lemma4 h =
  let History c s ch = h in
  match ch with
  | [] -> Vc.hbeq_reflexive c
  | x::xs -> 
      lemma4 x;
      assert (forall c. mem c x ==> Vc.hbeq (History?.clock h) c);
      admit ()
    
val lca : #n:nat 
        -> h:history n{wellformed h}
        -> a:Vc.t n 
        -> b:Vc.t n 
        -> init:Vc.t n{Vc.hbeq init a /\ Vc.hbeq init b}
        -> Tot (r:Vc.t n{Vc.hbeq r a /\ Vc.hbeq r b}) (decreases %[h])
val lca' : #n:nat 
         -> l:list (history n){forall h. L.mem h l ==> wellformed h} 
         -> a:Vc.t n 
         -> b:Vc.t n 
         -> init:Vc.t n{Vc.hbeq init a /\ Vc.hbeq init b}
         -> Tot (r:Vc.t n{Vc.hbeq r a /\ Vc.hbeq r b}) (decreases %[l])
let rec lca h a b init =
  lemma1 h;
  lemma2 h;
  let History clock _ ch = h in
  assert (forall h. L.mem h ch ==> wellformed h);
  assert (forall h1 h2. L.mem h1 ch /\ L.mem h2 ch ==> length (History?.clock h1) = length (History?.clock h2));
  if Vc.hbeq init clock && Vc.hbeq clock a && Vc.hbeq clock b
  then lca' ch a b clock
  else init
and lca' l a b init =
  match l with
  | [] -> init 
  | x::xs -> lca' xs a b (lca x a b init)

val lemma4 : #n:nat
          -> h:history n{wellformed h}
          -> a:Vc.t n{mem a h}
          -> b:Vc.t n{mem b h}
          -> init:Vc.t n{init = History?.clock h}
          -> Lemma (ensures (Vc.hbeq init a /\ Vc.hbeq init b))
let lemma4 h a b init =
  let History clock _ _ = h in
  assert (clock = init);
  Vc.hbeq_reflexive 
  admit ()

val lca2 : #n:nat
       -> h:history n{wellformed h}
       -> a:Vc.t n{mem a h}
       -> b:Vc.t n{mem b h}
       -> r:Vc.t n{Vc.hbeq r a /\ Vc.hbeq r b}
let lca2 h a b = lca h a b (History?.clock h)
