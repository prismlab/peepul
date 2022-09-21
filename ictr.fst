module Ictr

open FStar.List.Tot

val get_id : #op:eqtype -> (nat * op) -> nat
let get_id (id, _) = id

val get_op : #op:eqtype -> (nat * op) -> op
let get_op (_, op) = op

val mem_id : #op:eqtype
           -> id:nat
           -> l:list (nat * op)
           -> Tot (b:bool{(exists op. mem (id,op) l) <==> b=true})
let rec mem_id n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || mem_id n xs

val unique_id : #op:eqtype 
              -> l:list (nat * op)
              -> Tot bool
let rec unique_id l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (mem_id id xs) && unique_id xs

val get_eve : #op:eqtype 
            -> id:nat 
            -> l:list (nat * op){unique_id l /\ mem_id id l}
            -> Tot (s:(nat * op) {get_id s = id /\ mem s l})
let rec get_eve id l =
  match l with
  |(id1, x)::xs -> if id = id1 then (id1, x) else get_eve id xs 

val forallb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a
            -> Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forallb #a f l = 
  match l with
  |[] -> true
  |hd::tl -> if f hd then forallb f tl else false

val existsb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a 
            -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true})
let rec existsb #a f l =
  match l with
  |[] -> false
  |hd::tl -> if f hd then true else existsb f tl

val sorted : #op:eqtype
           -> l:list(nat * op){unique_id l} -> bool
let rec sorted #op l =
  match l with
  |[] -> true
  |x::[] -> true
  |x::xs -> forallb (fun (e:(nat * op)) -> fst x < fst e) xs && sorted xs

val filter : #a:eqtype
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ f e})
let rec filter #a f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

/////////////////////////////////////////

type op =
  |Inc

///SEQUENTIAL DATA TYPE IMPLEMENTATION///

type s = nat

let init = 0

val do : s -> (nat * op) -> s
let do s (_, Inc) = s + 1

val spec : s1:s -> o1:(nat * op) -> o2:(nat * op) -> s
let spec s1 o1 o2 =
  do (do s1 o1) o2

val fold : st:s -> l:list (nat * op){unique_id l} -> Tot s (decreases l)
let rec fold s l =
  match l with
  |[] -> s
  |x::xs -> fold (do s x) xs

////////////MRDT IMPLEMENTATION////////////

type s' = nat

val init' : nat
let init' = 0

let pre_cond_do' s o = true

val do' : st:s' -> (nat * op) -> r:s'
let do' s' (_, Inc) = s' + 1

val fold' : st:s' -> l:list (nat * op){unique_id l} -> Tot (st':s' {(st' >= st) /\ (st' = st + length l)})
            (decreases l)
let rec fold' s l =
  match l with
  |[] -> s
  |x::xs -> fold' (do' s x) xs

val pre_cond_merge' : l:s' -> a:s' -> b:s' -> bool
let pre_cond_merge' l a b = a >= l && b >= l

val merge' : l:s' 
           -> a:s'
           -> b:s'
           -> Pure s'
             (requires pre_cond_merge' l a b)
             (ensures (fun r -> r = a + b - l))
let merge' l a b =
  a + b - l

////////////////////////////////////////////

val eq : st:s -> st':s' -> bool
let eq s s' = s = s'

val eq_m : a:s' -> b:s' -> bool
let eq_m a b = a = b

val prop_init : unit -> Lemma (ensures (eq init init'))
let prop_init () = ()

val prop_equivalence : a:s' -> b:s' -> o:(nat * op)
                     -> Lemma (requires (eq_m a b /\ pre_cond_do' a o /\ pre_cond_do' b o))
                             (ensures (eq_m (do' a o) (do' b o)))
let prop_equivalence a b o = ()

val prop_do : st:s -> st':s' -> o:(nat * op)
            -> Lemma (requires (eq st st'))
                    (ensures (eq (do st o) (do' st' o)))
let prop_do s s' op = ()

val inverse : s:s'{s > 0} -> o:(nat * op) -> r:s'{s = do' r o}
let inverse a o = a - 1

val append : l1:list(nat * op) -> l2:list(nat * op)
           -> Pure (list (nat * op))
                  (requires (forall e. mem e l1 ==> not (mem_id (get_id e) l2)) /\
                            unique_id l1 /\ unique_id l2)
                  (ensures (fun r -> (forall e. mem e r <==> mem e l1 \/ mem e l2) /\ unique_id r))
                  (decreases %[l1;l2])
let rec append l1 l2 =
  match l1, l2 with
  |[],[] -> []
  |x::xs,_ -> x::(append xs l2)
  |[],x::xs -> x::(append [] xs)

val prop_merge1 : l:s' -> a:s' -> b:s' 
                -> atr:list(nat * op) -> o1:(nat * op) 
                -> btr:list(nat * op) -> o2:(nat * op) 
                -> Lemma (requires (unique_id atr /\ unique_id btr /\ get_id o1 <> get_id o2 /\
                                  (forall e. mem e atr ==> not (mem_id (get_id e) btr)) /\
                                  not (mem_id (get_id o1) atr) /\ not (mem_id (get_id o1) btr) /\
                                  not (mem_id (get_id o2) atr) /\ not (mem_id (get_id o2) btr) /\
                                  a = fold' l (append atr [o1]) /\ b = fold' l (append btr [o2])))
                        (ensures (let merge_prefix = (merge' l (inverse a o1) (inverse b o2)) in 
                                      ((merge' l a b) = (merge' merge_prefix (do' merge_prefix o1) (do' merge_prefix o2)))))
let prop_merge1 l a b atr_p o1 btr_p o2 = ()

val prop_merge2 : l:s' -> a:s' -> b:s' -> op1:(nat * op) -> op2:(nat * op)
                -> Lemma (requires (a = do' l op1 /\ b = do' l op2 /\ get_id op1 <> get_id op2))
                        (ensures (pre_cond_merge' l a b) /\
                                 (forall sl. eq sl l ==> (eq (spec sl op1 op2) (merge' l a b))))
let prop_merge2 l a b opa opb = ()

(*)val prop_merge3 : l:s' -> a:s' -> atr:list(nat * op) -> o1:(nat * op)
                -> Lemma (requires (unique_id atr /\ (forall e. mem e atr ==> get_id o1 <> get_id e)) /\
                                  (a = fold' l (append atr [o1])))
                        (ensures (merge' l a l) = (merge' l (inverse a o1) (do' l o1) ))
let prop_merge3 l a atr o1 = ()*)

val prop_merge4 : l:s' -> a:s' -> op1:(nat * op)
                -> Lemma (requires (a = do' l op1))
                        (ensures (pre_cond_merge' l a l) /\
                                 (forall sl. eq sl l ==> (eq (do sl op1) (merge' l a l))))
let prop_merge4 l a op1 = ()

val idempotence : a:s'
                -> Lemma (ensures (a = (merge' a a a)))
let idempotence a = ()

val commutativity : l:s' 
                  -> a:s'
                  -> b:s'
                  -> Lemma (requires (exists atr btr. a = fold' l atr /\ b = fold' l btr))
                          (ensures (merge' l b a = merge' l a b))
let commutativity l a b = ()

val associativity : l:s'
                  -> a:s'
                  -> b:s'
                  -> c:s'
                  -> Lemma (requires (exists atr btr ctr. a = fold' l atr /\ b = fold' l btr /\ c = fold' l ctr))
                          (ensures (merge' l a (merge' l b c) = merge' l (merge' l a b) c))
let associativity l a b c = ()



