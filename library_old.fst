module Library_old

open FStar.List.Tot
open FStar.All

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

(* Abstract state *)
noeq type ae (op:eqtype) = 
  |A : vis:((nat * op) -> (nat * op) -> Tot bool) 
     -> l:list (nat * op) {unique_id l /\ (forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ get_id e <> get_id e' /\ 
                                                    get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ vis e e' /\ vis e' e'') 
                                                    ==> vis e e'') (*transitive*) /\ 
                                      (forall e e'. (mem e l /\ mem e' l /\ get_id e <> get_id e' /\ vis e e') 
                                                ==> not (vis e' e)) (*asymmetric*) /\
                                      (forall e. mem e l ==> not (vis e e) (*irreflexive*)) /\
                                      (forall e e'. mem e l /\ mem e' l /\ get_id e <> get_id e' /\ vis e e' ==> get_id e < get_id e') /\
                                      (forall e e'. mem e l /\ mem e' l /\ get_id e = get_id e' ==> e = e') /\
                                      (forall e. mem e l ==> get_id e > 0)} -> ae op

val append : #op:eqtype 
           -> tr:ae op
           -> op1:(nat *op)
           -> Pure (ae op)
             (requires (forall e. mem e tr.l ==> get_id e < get_id op1) /\
                             get_id op1 > 0 /\ not (mem_id (get_id op1) tr.l))
             (ensures (fun r -> (forall e. mem e r.l <==> mem e tr.l \/ e = op1) /\ get_id op1 > 0 /\
                             (forall e e1. (mem e r.l /\ mem e1 r.l /\ get_id e <> get_id e1 /\ r.vis e e1) <==>
                                      (mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1) \/
                                      (mem e tr.l /\ e1 = op1 /\ get_id e <> get_id op1))))

#set-options "--z3rlimit 1000"
let append tr op = 
  (A (fun o o1 -> ((mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                (mem o tr.l && o1 = op && get_id o <> get_id op))) (op::tr.l))

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

val filter : #a:eqtype
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ f e})
let rec filter #a f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

val visib : #op:eqtype 
          -> id:nat 
          -> id1:nat {id <> id1}
          -> l:ae op
          -> Tot (b:bool {b = true <==> (exists e e1. mem e l.l /\ mem e1 l.l /\ get_id e = id /\ get_id e1 = id1 /\ l.vis e e1)})
let visib #op id id1 l =
  if (existsb (fun e -> get_id e = id && (existsb (fun e1 -> get_id e1 = id1 && l.vis e e1) l.l)) l.l)
    then true else false

val union1 : #op:eqtype
           -> l:ae op
           -> a:ae op
           -> Pure (list (nat * op))
             (requires (forall e. (mem e l.l ==> not (mem_id  (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique_id u))) 
             (decreases %[l.l;a.l])

#set-options "--z3rlimit 10000"
let rec union1 #op l a =
  match l,a with
  |(A _ []), (A _ []) -> []
  |(A _ (x::xs)), _ -> x::(union1  (A l.vis xs) a)
  |(A _ []), (A _ (x::xs)) -> x::(union1 l (A a.vis xs))

val union : #op:eqtype 
          -> l:ae op
          -> a:ae op
          -> Pure (ae op)
            (requires (forall e. (mem e l.l ==> not (mem_id (get_id e) a.l))))
            (ensures (fun u -> (forall e e1. (mem e l.l /\ mem e1 l.l /\ get_id e <> get_id e1 /\ l.vis e e1) \/
                                     (mem e a.l /\ mem e1 a.l /\ get_id e <> get_id e1 /\ a.vis e e1) ==>
                                     (mem e u.l /\ mem e1 u.l /\ get_id e <> get_id e1 /\ u.vis e e1)))) 
let union l a =
  (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
               (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1)) (union1 l a))

val absmerge1 : #op:eqtype 
              -> l:ae op
              -> a:ae op
              -> b:ae op
              -> Pure (list (nat * op))
                (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                          (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                          (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))
                (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique_id u))) 
                (decreases %[l.l;a.l;b.l])
#set-options "--z3rlimit 1000"
let rec absmerge1 #op l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> []
  |(A _ (x::xs)), _, _ -> x::(absmerge1 (A l.vis xs) a b)
  |(A _ []), (A _ (x::xs)), _ -> x::(absmerge1 l (A a.vis xs) b)
  |(A _ []), (A _ []), (A _ (x::xs)) -> x::(absmerge1 l a (A b.vis xs))

val absmerge : #op:eqtype 
             -> l:ae op
             -> a:ae op
             -> b:ae op
             -> Pure (ae op)
               (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                         (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))  
               (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                               (forall e1 e2. (mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/ 
                                         (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) ==>
                                         (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2))))
#set-options "--z3rlimit 1000"
let absmerge l a b = 
  (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) || 
               (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) || 
               (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1)) (absmerge1 l a b))

val remove_op1 : #op:eqtype 
               -> tr:ae op 
               -> x:(nat * op) 
               -> Pure (list (nat * op))
                 (requires (mem x tr.l))
                 (ensures (fun r -> (forall e. mem e r <==> mem e tr.l /\ e <> x) /\ unique_id r /\ 
                                 (List.Tot.length r = List.Tot.length tr.l - 1)))
                 (decreases tr.l)

let rec remove_op1 #op tr x =
  match tr.l with
  |x1::xs -> if x = x1 then xs else x1::remove_op1 (A tr.vis xs) x

val remove_op : #op:eqtype 
              -> tr:ae op 
              -> x:(nat * op) 
              -> Pure (ae op)
                     (requires (mem x tr.l))
                     (ensures (fun r -> (forall e. mem e r.l <==> mem e tr.l /\ e <> x) /\ unique_id r.l /\
                                     (forall e e1. mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ e <> x /\ e1 <> x /\ tr.vis e e1 <==>
                                              mem e (remove_op1 tr x) /\ mem e1 (remove_op1 tr x) /\ get_id e <> get_id e1 
                                              /\ tr.vis e e1) /\ (List.Tot.length r.l = List.Tot.length tr.l - 1)))
                     (decreases tr.l)
let remove_op #op tr x =
    (A (fun o o1 -> mem o (remove_op1 tr x) && mem o1 (remove_op1 tr x) && get_id o <> get_id o1 && tr.vis o o1) (remove_op1 tr x))

val filter_uni : #op:eqtype
               -> f:((nat * op) -> bool)
               -> l:list (nat * op)
               -> Lemma (requires unique_id l)
                       (ensures (unique_id (filter f l)))
                          [SMTPat (filter f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

(*)class mrdt (s:eqtype (*state*)) (op:eqtype (*operations*)) = {

  init : s;

  (*Pre-condition for apply operation*)
  pre_cond_op : s
              -> (nat (*timestamp*) * op)
              -> Tot bool;

  (*Implementation of operations*)
  app_op : st:s
         -> op:(nat (*timestamp*) * op)
         -> Pure s (requires pre_cond_op st op)
                  (ensures (fun r -> true));

  (* Simulation relation *)
  sim : ae op -> s -> Tot bool;

  (*Pre-condition for three-way merge*)
  pre_cond_merge : ltr:ae op 
                 -> l:s 
                 -> atr:ae op 
                 -> a:s
                 -> btr:ae op 
                 -> b:s 
                 -> Tot bool;

  pre_cond_merge1 : s -> s -> s 
                  -> Tot bool;

  merge1 : l:s
         -> a:s
         -> b:s
         -> Pure s (requires pre_cond_merge1 l a b)
                  (ensures (fun r -> true));
  
  (*Implementation of three-way*)
  merge : ltr:ae op 
        -> l:s 
        -> atr:ae op 
        -> a:s
        -> btr:ae op 
        -> b:s 
        -> Pure s (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                           (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                           (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                           (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                           pre_cond_merge1 l a b /\ pre_cond_merge ltr l atr a btr b)
                 (ensures (fun r -> r = merge1 l a b));

  (*Proof of three-way merge*)
  prop_merge : ltr:ae op 
             -> l:s 
             -> atr:ae op 
             -> a:s 
             -> btr:ae op
             -> b:s
             -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                               (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                               (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                               (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                               pre_cond_merge1 l a b /\ pre_cond_merge ltr l atr a btr b)
                     (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)));

  (*Proof of apply operation*)
  prop_oper : tr:ae op 
            -> st:s 
            -> op:(nat * op)
            -> Lemma (requires (sim tr st) /\ pre_cond_op st op /\ 
                              (forall e. mem e tr.l ==> get_id e < get_id op) /\
                              get_id op > 0 /\ not (mem_id (get_id op) tr.l))
                    (ensures (sim (append tr op) (app_op st op)));

  (*Convergence modulo observable behavior*)
  convergence : tr:ae op
              -> a:s
              -> b:s
              -> Lemma (requires (sim tr a /\ sim tr b))
                      (ensures true)
  }
 
*)
