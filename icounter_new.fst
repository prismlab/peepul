module Ictr_correct_sim

open FStar.List.Tot

type op =
  |Inc : nat -> op

type o = (nat (*unique id*) * op)

let get_id (id,_) = id
let get_op (_,op) = op
let get_ele (_,Inc n) = n

type s = nat

val app_op : s -> o -> s
let app_op c (_,Inc n) = c + n

val member : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists op. mem (id,op) l) <==> b=true})
let rec member n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member n xs

val unique : l:list o
           -> Tot bool
let rec unique l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member id xs) && unique xs

noeq type ae = 
|A : vis:(o -> o -> Tot bool) -> l:list o {unique l} -> ae

assume val axiom : l:ae
                 -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\ 
                         get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*)/\ 
                         (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                         (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*)))
                         [SMTPat (unique l.l)]

(*)noeq type ae  =
       |A : vis : (o -> o -> Tot bool)
         -> l:(list o) {(unique l) /\
                       (forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ get_id e <> get_id e' /\ get_id e' <> get_id e'' /\ get_id e <> get_id e''  /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\ 
                       (forall e e'. (mem e l /\ mem e' l /\ get_id e <> get_id e' /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                       (forall e. mem e l ==> not (vis e e) (*irreflexive*))}  
         -> ae*)


val sum : l:(list o) -> Tot nat (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |((_,Inc n)::xs) -> n + sum xs

#set-options "--query_stats"              
val sim : s0:s
        -> tr:ae
        -> s1:s 
        -> Tot (b: bool {(s1 = s0 + sum tr.l) <==> b = true}) 
let sim s0 tr s1 = (s1 = s0 + sum tr.l)

val absmerge1 : l:ae
             -> a:ae 
             -> b:ae
             -> Pure (list o)
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                         (forall e. mem e b.l ==> not (member (get_id e) l.l)))
               (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique u)))
               (decreases %[l.l;a.l;b.l])
let rec absmerge1 l a b =
    match l,a,b with
    |(A _ []), (A _ []), (A _ []) -> []
    |(A _ (x::xs)), _, _ -> x::(absmerge1 (A l.vis xs) a b)
    |(A _ []), (A _ (x::xs)), _ -> x::(absmerge1 l (A a.vis xs) b)
    |(A _ []), (A _ []), (A _ (x::xs)) -> x::(absmerge1 l a (A b.vis xs))
    
val absmerge : l:ae
             -> a:ae
             -> b:ae
             -> Pure ae 
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                         (forall e. mem e b.l ==> not (member (get_id e) l.l)))
                (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                                (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2) <==> 
                                          (mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                          (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/ 
                                          (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) \/
                                          (mem e1 l.l /\ mem e2 a.l /\ get_id e1 <> get_id e2) \/
                                          (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2))))

let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1) || 
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1)) (absmerge1 l a b))

val lemma1 : l:ae
           -> a:ae
           -> b:ae
           -> Lemma
             (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                       (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                       (forall e. mem e b.l ==> not (member (get_id e) l.l)))
             (ensures (forall e. mem e (absmerge1 l a b) <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                      (sum (absmerge l a b).l = sum a.l + sum b.l + sum l.l))
             (decreases %[l.l;a.l;b.l])
let rec lemma1 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma1 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma1 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma1 l a (A b.vis xs)

val merge : s0:s
          -> ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (sim s0 ltr l /\ sim l atr a /\ sim l btr b) /\ 
                             (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e btr.l ==> not (member (get_id e) ltr.l)))
                   (ensures (fun res -> true))   
let merge s0 ltr l atr a btr b = 
  a + b - l

val prop_merge : s0:s
               -> ltr:ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (sim s0 ltr l /\ sim l atr a /\ sim l btr b) /\ 
                                 (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e btr.l ==> not (member (get_id e) ltr.l)))
                       (ensures (sim s0 (absmerge ltr atr btr) (merge s0 ltr l atr a btr b)))
let prop_merge s0 ltr l atr a btr b =
    lemma1 ltr atr btr; ()
(*383 ms*)

val append1 : tr:ae
            -> op:o
            -> Pure (list o)
              (requires (not (member (get_id op) tr.l)))
              (ensures (fun res -> (forall e. mem e res <==> mem e tr.l \/ e = op)))
let append1 tr op = (op::tr.l)

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member (get_id op) tr.l)))
             (ensures (fun res -> (forall e. mem e res.l <==> mem e tr.l \/ e = op) /\
                               (forall e1 e2. (mem e1 res.l /\ mem e2 res.l /\ get_id e1 <> get_id e2 /\ res.vis e1 e2) <==> 
                                         (mem e1 tr.l /\ mem e2 tr.l /\ get_id e1 <> get_id e2 /\ tr.vis e1 e2) \/
                                         (mem e1 tr.l /\ e2 = op /\ get_id e1 <> get_id e2))))
let append tr op =
    (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                 (mem o tr.l && o1 = op && get_id o <> get_id op)) (append1 tr op))

val prop_oper : s0:s
              -> tr:ae
              -> st:s
              -> op:o 
              -> Lemma (requires (sim s0 tr st) /\ 
                                (not (member (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> mem op (append tr op).l /\ (append tr op).vis e op))
                      (ensures (sim s0 (append tr op) (app_op st op)))
let prop_oper s0 tr st op = ()

val convergence : s0:s
                -> tr:ae
                -> a:s
                -> b:s  
                -> Lemma (requires (sim s0 tr a /\ sim s0 tr b))
                        (ensures (a = b))
let convergence s0 tr a b = ()
