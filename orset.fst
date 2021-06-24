module Orset

open FStar.List.Tot

type op =
    | Add
    | Rem

type o = (nat (*unique id*) * op * nat (*element*))

let get_id (id,_,_) = id
let get_op (_,op,_) = op
let get_ele (_,_,ele) = ele

val member_s : id:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_s n l =
    match l with
    |[] -> false
    |(id,_)::xs -> (n = id) || member_s n xs

val unique_s : l:list (nat * nat)
             -> Tot bool
let rec unique_s l =
    match l with
    |[] -> true
    |(id,_)::xs -> not (member_s id xs) && unique_s xs

type s = 
  |S : add : list (nat (*unique id*)* nat (*ele*)) {unique_s add}
     -> rem : list (nat (*unique id*)* nat (*ele*)) {(forall e. mem e rem ==> mem e add) /\ unique_s rem}
     -> s

val forallb : #a:eqtype 
            -> f:(a -> bool)
            -> l:list a 
            -> Tot(b:bool{(forall e. mem e l ==> f e) <==> b = true})
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

val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat) 
               -> Lemma (requires (unique_s l))
                       (ensures (unique_s (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
    match l with
    |[] -> ()
    |x::xs -> filter_uni f xs

val un : a:list (nat * nat)
       -> b:list (nat * nat)
       -> Pure (list (nat * nat))
              (requires (unique_s a /\ unique_s b))
              (ensures (fun res -> (forall e. member_s e res <==> member_s e a \/ member_s e b) /\
                                (forall e. mem e res ==> mem e a \/ mem e b) /\ unique_s res))
let rec un a b =
          match a,b with
          |[],[] -> []
          |x::xs,_ -> if (member_s (fst x) b) then un xs b else x::(un xs b)
          |[],b -> b

val app_op : s1:s
           -> op:o 
           -> Pure s
                  (requires not (member_s (get_id op) s1.add))
                  (ensures (fun res -> (get_op op = Add ==> mem ((get_id op),(get_ele op)) res.add) /\
                                    (get_op op = Rem ==> (forall e. mem e res.rem /\ snd e = get_ele op <==> 
                                                               snd e = get_ele op /\ mem e s1.add)) /\
                                    (forall e. mem e s1.add ==> mem e res.add) /\
                                    (forall e. mem e res.rem ==> mem e s1.add)))
let rec app_op (S add rem) (id, op, ele) =
  match op with
  |Add -> (S ((id, ele)::add) rem) 
  |Rem -> let lst = (filter (fun s -> snd s = ele) add) in
         let lst1 = un lst rem in
  (S add lst)

val member : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists n ele. mem (id,n,ele) l) <==> b=true})
let rec member n l =
  match l with
  |[] -> false
  |(id,_,_)::xs -> (n = id) || member n xs

val unique : l:list o
           -> Tot bool
let rec unique l =
  match l with
  |[] -> true
  |(id,_,_)::xs -> not (member id xs) && unique xs

noeq type ae  =
     |A : vis : (o -> o -> Tot bool)
        -> l:(list o) {(forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\ 
                      (forall e e'. (mem e l /\ mem e' l /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                      (forall e. mem e l ==> not (vis e e) (*irreflexive*) /\
                      (unique l))}  
        -> ae

#set-options "--query_stats"              
val sim : tr:ae
        -> s1:s 
        -> Tot (bool) 
let rec sim tr s1 =
  let lst = (filter (fun a -> (get_op a = Add)) tr.l) in
  let lst1 = (filter (fun a -> (existsb (fun r -> (get_op r = Rem && get_ele r = get_ele a && tr.vis a r)) tr.l)) lst) in

  forallb (fun e -> mem ((get_id e), (get_ele e)) s1.add) lst &&
  forallb (fun e -> mem ((fst e), Add, (snd e)) lst) s1.add &&
  forallb (fun e -> mem ((get_id e), (get_ele e)) s1.rem) lst1 &&
  forallb (fun e -> mem ((fst e), Add, (snd e)) lst1) s1.rem

val rem1 : l:ae 
         -> op:o
         -> Pure (list o)
           (requires true)
           (ensures (fun r -> ((forall e. mem e r ==> mem e l.l) /\ (unique r)))) (decreases %[l.l])
let rec rem1 l op =
    match l with 
    |(A _ []) -> []
    |(A _ (x::xs)) -> if (x = op) then xs else (x::(rem1 (A l.vis xs) op))

val rem : l:ae 
        -> op:o
        -> Pure ae
          (requires true)
          (ensures (fun r -> ((forall e. mem e r.l ==> mem e l.l) /\
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
             (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l) /\
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
            (ensures (fun u -> (forall e. mem e u.l <==> mem e a.l \/ mem e b.l) /\
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

val diff2 : a:list (nat * nat)
          -> l:list (nat * nat)
          -> Pure (list (nat * nat))
                 (requires (unique_s a /\ unique_s l))
                 (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\ unique_s d )) (decreases %[l;a;l;a])
let rec diff2 a l = 
    filter (fun e -> not (mem e l)) a

val un2 : a:list (nat * nat)
        -> b:list (nat * nat)
        -> Pure (list (nat * nat))
               (requires (unique_s a /\ unique_s b) /\ (forall e. mem e a ==> not (member_s (fst e) b)))
               (ensures (fun res -> (forall e. mem e res <==> mem e a \/ mem e b) /\ unique_s res))
let rec un2 a b =
            match a,b with
            |[],[] -> []
            |x::xs,_ -> x::(un2 xs b)
            |[],b -> b

val lemma1 : ltr:ae
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
                    (ensures (forall e. mem e (diff2 a.add l.add) ==> not (member_s (fst e) b.add)) /\
                             (forall e. mem e (diff2 b.add l.add) ==> not (member_s (fst e) a.add)) /\
                             (forall e. mem e (diff2 a.rem l.rem) ==> not (member_s (fst e) b.rem)) /\
                             (forall e. mem e (diff2 b.rem l.rem) ==> not (member_s (fst e) a.rem)))
#set-options "--z3rlimit 50"
let lemma1 ltr l atr a btr b = ()

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
    let add = un2 l.add (un2 (diff2 a.add l.add) (diff2 b.add l.add)) in
    let rem = un2 l.rem (un2 (diff2 a.rem l.rem) (diff2 b.rem l.rem)) in
    (S add rem)

val sim1 : tr:ae
         -> s1:s 
         -> Tot (bool) 
let rec sim1 tr s1 =
  let lst = (filter (fun a -> (get_op a = Add)) tr.l) in
  let lst1 = (filter (fun a -> (existsb (fun r -> (get_op r = Rem && get_ele r = get_ele a && tr.vis a r)) tr.l)) lst) in

  forallb (fun e -> mem ((get_id e), (get_ele e)) s1.rem) lst1 &&
  forallb (fun e -> mem ((fst e), Add, (snd e)) lst1) s1.rem
    
val prop_rem : ltr: ae
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
                       (ensures (sim1 (absmerge ltr atr btr) (merge ltr l atr a btr b))) 

#set-options "--z3rlimit 10000"
let prop_rem ltr l atr a btr b = 
(*)assert (forall e. mem e (diff2 a.add l.add) ==> not (member_s (fst e) b.add) /\
       (forall e. mem e (diff2 b.add l.add) ==> not (member_s (fst e) a.add)) /\
       (forall e. mem e (diff2 a.rem l.rem) ==> not (member_s (fst e) b.rem)) /\
       (forall e. mem e (diff2 b.rem l.rem) ==> not (member_s (fst e) a.rem))); *)
lemma1 ltr l atr a btr b; ()

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

#set-options "--z3rlimit 100"
let prop_merge ltr l atr a btr b = 
  prop_rem ltr l atr a btr b; ()

val append : tr:ae
           -> op:o
           -> Pure ae
               (requires (not (member (get_id op) tr.l)))
               (ensures (fun res -> true)) (decreases tr.l)
let append tr op =
      match tr with
      |(A _ []) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::[]))
      |(A _ (x::xs)) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::(x::xs)))
      
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
                -> Lemma (requires  (sim tr a /\ sim tr b))
                        (ensures (forall e. mem e a.add <==> mem e b.add) /\
                                 (forall e. mem e a.rem <==> mem e b.rem))
let convergence tr a b = ()


(* Statistics: 

   prop_merge : separate sim for s1.rem:  forallb (fun e -> mem ((get_id e), (get_ele e)) s1.add) lst &&
     forallb (fun e -> mem ((fst e), Add, (snd e)) lst) s1.add &&
     forallb (fun e -> mem ((get_id e), (get_ele e)) s1.rem) lst1 &&
     forallb (fun e -> mem ((fst e), Add, (snd e)) lst1) s1.rem

   590364 ms or 9.83 min (--z3rlimit 10000) for prop_rem
   24934 ms or 0.41 min (--z3rlimit 100) for prop_merge 

prop_merge : sim : forallb (fun e -> mem ((get_id e), (get_ele e)) s1.add) lst &&
   forallb (fun e -> mem ((fst e), Add, (snd e)) lst) s1.add &&
   forallb (fun e -> mem ((get_id e), (get_ele e)) s1.rem) lst1 &&
   forallb (fun e -> (existsb (fun r -> snd e = get_ele r && get_op r = Rem) tr.l)) s1.rem
   
   53974 ms or 0.899 min (--z3rlimit 500)
   84463 ms or 1.40 min ( --z3rlimit 300)
*)
