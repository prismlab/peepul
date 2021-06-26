module Icounter

open FStar.List.Tot

type op =
  |Inc 

type o = (nat (*unique id*) * op)

let get_id (id,_) = id
let get_op (_,op) = op

type s = nat

val app_op : s -> o -> s
let app_op c (_,Inc) = c + 1

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

noeq type ae  =
     |A : vis : (o -> o -> Tot bool)
        -> l:(list o) {(forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\ 
                      (forall e e'. (mem e l /\ mem e' l /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                      (forall e. mem e l ==> not (vis e e) (*irreflexive*) /\
                      (unique l))}  
        -> ae

val sum : a:(list o) -> Tot nat (decreases a)
let rec sum l =
     match l with
     |[] -> 0
     |((_,Inc)::xs) -> 1 + sum xs
     
#set-options "--query_stats"              
val sim : tr:ae
        -> s1:s 
        -> Tot (bool) 
let sim tr s1 = (s1 = sum tr.l)

val rem1 : l:ae 
         -> op:o
         -> Pure (list o)
           (requires true)
           (ensures (fun r -> ((mem op l.l /\ l.l <> []) ==> (sum r = sum l.l - 1)) /\ 
                           ((forall e. mem e r ==> mem e l.l) /\ (unique r)))) (decreases %[l.l])
let rec rem1 l op =
    match l with 
    |(A _ []) -> []
    |(A _ (x::xs)) -> if (x = op) then xs else (x::(rem1 (A l.vis xs) op))

val rem : l:ae 
        -> op:o
        -> Pure ae
          (requires true)
          (ensures (fun r -> ((mem op l.l /\ l.l <> []) ==> (sum r.l = sum l.l - 1)) /\  
                          ((forall e. mem e r.l ==> mem e l.l) /\
                          (forall e e1. mem e r.l /\ mem e1 r.l /\ r.vis e e1 ==> mem e l.l /\ mem e1 l.l /\ l.vis e e1) /\
                          (forall e e1. (mem e r.l /\ mem e1 r.l /\ not (r.vis e e1)) ==> (mem e l.l /\ mem e1 l.l /\ not (l.vis e e1))) /\
                          (forall e e1. (mem e r.l /\ mem e1 r.l /\ not (r.vis e e1 || r.vis e1 e)) ==> 
                                   (mem e l.l /\ mem e1 l.l /\ not (l.vis e e1 || l.vis e1 e))))))
let rem l op =
  let res = (rem1 l op) in
  (A (fun o o1 -> mem o l.l && mem o1 l.l && l.vis o o1) res)

val diff1 : a:ae
          -> l:ae
          -> Pure (list o)
            (requires (forall e. mem e l.l ==> mem e a.l) /\ 
                      (forall e e1. mem e l.l /\ mem e1 l.l /\ l.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                      (forall e e1. (mem e l.l /\ mem e1 a.l ==> mem e a.l /\ a.vis e e1)))
            (ensures (fun d -> (forall e. mem e d <==> mem e a.l /\ not (mem e l.l)) /\
                            (sum d = sum a.l - sum l.l) /\
                            (forall e. mem e d ==> not (member (get_id e) l.l)))) (decreases %[l.l;a.l])
let rec diff1 a l = 
    match a,l with
    |_,(A _ []) -> a.l
    |_,(A _ (x::xs)) -> if (mem x a.l) then (diff1 (rem a x) (A l.vis xs)) else (diff1 a (A l.vis xs))

val diff : a:ae
         -> l:ae
         -> Pure ae
          (requires (forall e. mem e l.l ==> mem e a.l) /\ 
                    (forall e e1. mem e l.l /\ mem e1 l.l /\ l.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                    (forall e e1. (mem e l.l /\ mem e1 a.l ==> mem e a.l /\ a.vis e e1)))
          (ensures (fun d -> (forall e. mem e d.l <==> mem e a.l /\ not(mem e l.l)) /\
                          (forall e. mem e d.l ==> not (member (get_id e) l.l)) /\
                          (sum d.l = sum a.l - sum l.l) /\
                          (forall e e1. mem e d.l /\ mem e1 d.l /\ d.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1)) ==> (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1))) /\
                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1 || d.vis e1 e)) ==>
                                   (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e))))) (decreases l)
let diff a l =
  (A (fun o o1 -> mem o a.l && mem o1 a.l && a.vis o o1) (diff1 a l))

val union1 : a:ae 
           -> b:ae
           -> Pure (list o)
             (requires (forall e. (mem e a.l ==> not (member (get_id e) b.l))) /\
                             (forall e. (mem e b.l ==> not (member (get_id e) a.l))))
             (ensures (fun u -> (sum u = sum a.l + sum b.l) /\  
                             (forall e. mem e u <==> mem e a.l \/ mem e b.l) /\
                             (unique u)))     (decreases %[a.l;b.l])
let rec union1 a b =
  match a,b with
  |(A _ []),(A _ []) -> []
  |(A _ (x::xs)),_ -> x::(union1 (A (fun o o1 -> mem o a.l && mem o1 a.l && a.vis o o1) xs) b)
  |(A _ []), (A _ (x::xs)) -> x::(union1 a (A (fun o o1 -> mem o b.l && mem o1 b.l && b.vis o o1) xs))

val union : a:ae 
          -> b:ae
          -> Pure ae
            (requires (forall e. (mem e a.l ==> not (member (get_id e) b.l))) /\
                            (forall e. (mem e b.l ==> not (member (get_id e) a.l))))
            (ensures (fun u -> 
                            (forall e. mem e u.l <==> mem e a.l \/ mem e b.l) /\
                            (sum u.l = sum a.l + sum b.l) /\  
                            (forall e e1. (mem e u.l /\ mem e1 u.l /\ u.vis e e1) <==> 
                                     ((mem e a.l /\ mem e1 a.l /\ a.vis e e1) \/ (mem e b.l /\ mem e1 b.l /\ b.vis e e1))) /\
                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e) ==> 
                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1 || b.vis e1 e) ==> 
                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e))))
let union a b = 
  (A (fun o o1 -> (mem o a.l && mem o1 a.l && a.vis o o1) || (mem o b.l && mem o1 b.l && b.vis o o1)) (union1 a b))

val absmerge : l:ae
             -> a:ae
             -> b:ae
             -> Pure ae 
               (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                         (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> 
                                   mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\ mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                         (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                         (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                         (forall e. mem e (diff a l).l ==> not (member (get_id e) b.l)) /\
                         (forall e1. mem e1 (diff b l).l ==> not (member (get_id e1) a.l)))  
                (ensures (fun u ->(forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\ 
                               (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ u.vis e1 e2) <==> 
                                         (mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2) \/ 
                                         (mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2)) /\ 
                              (forall e e1. mem e l.l /\ mem e1 l.l /\ not (l.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e l.l /\ mem e1 l.l /\ not (l.vis e e1 || l.vis e1 e) ==> 
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                              (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e) ==>
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                              (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1 || b.vis e1 e) ==> 
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e))))
                                       
let absmerge l a b = 
    let la = diff a l in
    let lb = diff b l in
    let u1 = union la lb in
    let res = union l u1 in
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && b.vis o o1)) res.l)

val lemma : ltr:ae 
          -> l:s 
          -> atr:ae 
          -> a:s 
          -> Lemma (ensures (sim ltr l /\ sim atr a /\
                           (forall e. mem e ltr.l ==> mem e atr.l) /\
                           (forall e e1. mem e ltr.l /\ mem e1 atr.l  ==> mem e atr.l /\ atr.vis e e1)) ==> a >= l)
                           (decreases %[ltr.l;atr.l])
let rec lemma ltr l atr a = 
    match ltr,atr with
    |(A _ []), (A _ []) -> ()
    |(A _ (x::xs)), _ -> lemma (A ltr.vis xs) l atr a
    |(A _ []), (A _ (x::xs)) -> lemma ltr l (A atr.vis xs) a

val merge : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                             (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                             (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                       (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                        mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                             (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))
                   (ensures (fun res -> true))                         

let merge ltr l atr a btr b = 
      lemma ltr l atr a;
      lemma ltr l btr b;
      a + b - l

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member (get_id op) tr.l)))
             (ensures (fun res -> true)) (decreases tr.l)
let append tr op =
    match tr with
    |(A _ []) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::[]))
    |(A _ (x::xs)) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::(x::xs)))

val prop_merge : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                                 (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                                 (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                           (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                           mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                                 (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))                        
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b))) 

#set-options "--z3rlimit 30"
let prop_merge ltr l atr a btr b = ()
 
val prop_oper : tr:ae
              -> st:s
              -> op:o 
              -> Lemma (requires (sim tr st) /\ 
                                (not (member (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> (append tr op).vis e op))
                      (ensures (sim (append tr op) (app_op st op))) (decreases %[tr.l])
let prop_oper tr st op = ()

val convergence : tr:ae
                -> a:s
                -> b:s  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (a = b))
let convergence tr a b = ()
