module Orset_opt

open FStar.List.Tot

type op =
  |Add : nat (*element*) -> op
  |Rem : nat (*element*) -> op

type o = (nat (*unique id*) * op)

val get_id : o1:o -> Tot (n:nat {exists op. o1 = (n, op)})
let get_id (id, _) = id

val opa : o1:o -> Tot (b:bool {b = true <==> (exists id e. o1 = (id, Add e))})
let opa o =
  match o with
  |(_, (Add _)) -> true
  |(_, (Rem _)) -> false

val opr : o1:o -> Tot (b:bool {b = true <==> (exists id e. o1 = (id, Rem e))})
let opr o =
  match o with
  |(_, (Add _)) -> false
  |(_, (Rem _)) -> true

val get_ele : o1:o -> Tot (n:nat {exists id. (o1 = (id, Add n)) \/ (o1 = (id, Rem n))})
let get_ele o =
  match o with
  |(_, (Add ele)) -> ele
  |(_, (Rem ele)) -> ele

val member_id : id:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_id n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_id n xs

val member_ele : ele:nat
               -> l:list (nat * nat)
               -> Tot (b:bool{(exists id. mem (id,ele) l) <==> b=true})
let rec member_ele ele l =
    match l with
    |[] -> false
    |(_,ele1)::xs -> (ele = ele1) || member_ele ele xs

val unique_id : l:list (nat * nat)
             -> Tot bool
let rec unique_id l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_id id xs) && unique_id xs

val unique_ele : l:list (nat * nat)
               -> Tot bool
let rec unique_ele l =
    match l with
    |[] -> true
    |(_,ele)::xs -> not (member_ele ele xs) && unique_ele xs

type s = l:list (nat (*unique id*)* nat (*ele*)) {unique_id l /\ unique_ele l}

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

val except : #a:eqtype 
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ not (f e)})
let rec except #a f l =
  match l with
  |[] -> []
  |hd::tl -> if not (f hd) then hd::(except f tl) else except f tl

val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat) 
               -> Lemma (requires (unique_id l /\ unique_ele l))
                       (ensures (unique_id (filter f l) /\ unique_ele (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val update : s1:s
           -> ele:nat
           -> id:nat
           -> Pure s
             (requires (member_ele ele s1) /\ not (member_id id s1))
             (ensures (fun u -> (forall e. mem e s1 /\ snd e <> ele <==> mem e u /\ snd e <> ele) /\
                       (forall e. mem e u /\ fst e <> id /\ member_id (fst e) u <==> mem e s1 /\ snd e <> ele /\ member_id (fst e) s1) /\
                             (forall e. member_ele e s1 <==> member_ele e u) /\
                             (forall e. mem e u /\ e <> (id,ele) <==> mem e s1 /\ snd e <> ele) /\
                             mem (id,ele) u))
                             (decreases s1)
let rec update s1 ele id =
  match s1 with
  |[] -> []
  |(id1,ele1)::xs -> if ele = ele1 then (id,ele1)::xs else (id1,ele1):: update xs ele id

val remove_ele : s1:s
               -> ele:nat
               -> Pure s
               (requires (member_ele ele s1))
               (ensures (fun u -> (forall e. mem e s1 /\ snd e <> ele <==> mem e u)))
                               (decreases s1)
let rec remove_ele s1 ele =
    match s1 with
    |[] -> []
    |(id1,ele1)::xs -> if ele = ele1 then xs else (id1,ele1):: remove_ele xs ele

val app_op : s1:s
           -> op:o 
           -> Pure s
             (requires (not (member_id (get_id op) s1)))
             (ensures (fun res -> (opa op ==> (forall e. mem e s1 /\ snd e <> get_ele op <==> mem e res /\ snd e <> get_ele op) /\
                                          (forall e. mem e res /\ fst e <> get_id op /\ member_id (fst e) res <==> mem e s1 /\ snd e <> get_ele op /\ member_id (fst e) s1) /\
                                          (forall e. member_ele e s1 \/ e = get_ele op <==> member_ele e res) /\
                                          (forall e. mem e res /\ e <> ((get_id op), (get_ele op)) <==> mem e s1 /\ snd e <> get_ele op) /\
                                            mem ((get_id op), (get_ele op)) res) /\
                               (opr op ==> (forall e. mem e res <==> mem e s1 /\ snd e <> get_ele op))))
let app_op s1 op =
    if (opa op) 
      then (if member_ele (get_ele op) s1 then (update s1 (get_ele op) (get_id op)) else ((get_id op),(get_ele op))::s1) 
        else (if member_ele (get_ele op) s1 then (remove_ele s1 (get_ele op)) else s1)

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

val fst : nat * nat -> nat
let fst (id,ele) = id
val snd : nat * nat -> nat
let snd (id,ele) = ele

#set-options "--query_stats"
val sim : tr:ae
        -> s1:s 
        -> Tot (b:bool {(b = true <==> (forall e. mem e s1 ==> (forall a. mem a tr.l /\ opa a /\ snd e = get_ele a ==>
                       (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r ==> 
                        not (get_id a <> get_id r && tr.vis a r)) ==> fst e >= get_id a) /\ 
                       (mem ((fst e), Add (snd e)) tr.l /\
              (forall r. mem r tr.l /\ opr r /\ get_ele r = snd e ==> not (fst e <> get_id r && tr.vis ((fst e), Add (snd e)) r)))) /\
                (forall a. mem a tr.l /\ opa a ==> (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r && get_id a <> get_id r ==> not (tr.vis a r)) ==> member_ele (get_ele a) s1))})

#set-options "--z3rlimit 1000000"
let sim tr s1 = 
  let lsta = (filter (fun a -> opa a) tr.l) in
  let lstr = (filter (fun r -> opr r) tr.l) in
  let lst = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in
 
  (forallb (fun e -> (forallb (fun a -> fst e >= get_id a) (filter (fun a -> get_ele a = snd e) lst)) &&
                  (mem ((fst e), Add (snd e)) tr.l && 
                  not (existsb (fun r -> fst e <> get_id r && tr.vis ((fst e), Add (snd e)) r ) 
                  (filter (fun r -> snd e = get_ele r) lstr)))) s1) &&
  (forallb (fun a -> member_ele (get_ele a) s1) lst)

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member (get_id op) tr.l)))
             (ensures (fun res -> true)) 
let append tr op =
  match tr with
  |(A _ []) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                           (mem o tr.l && o1 = op && get_id o <> get_id op)) (op::[]))
  |(A _ (x::xs)) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                               (mem o tr.l && o1 = op && get_id o <> get_id op)) (op::(x::xs)))

val prop_oper : tr:ae
              -> st:s
              -> op:o 
              -> Lemma (requires (sim tr st) /\ 
                                (not (member (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op))
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op =
  assert (not (member_id (get_id op) st)); 
  ()
 (*45366 ms*)

val convergence : tr:ae
                  -> a:s
                  -> b:s  
                  -> Lemma (requires (sim tr a /\ sim tr b))
                          (ensures (forall e. mem e a <==> mem e b))
let convergence tr a b = ()

val union1 : l:ae
           -> a:ae
           -> Pure (list o)
             (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique u))) (decreases %[l.l;a.l])
let rec union1 l a =
  match l,a with
  |(A _ []), (A _ []) -> []
  |(A _ (x::xs)), _ -> x::(union1 (A l.vis xs) a)
  |(A _ []), (A _ (x::xs)) -> x::(union1 l (A a.vis xs))

val union : l:ae
          -> a:ae
          -> Pure ae
            (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))))
            (ensures (fun u -> (forall e e1. (mem e u.l /\ mem e1 u.l /\ get_id e <> get_id e1 /\ u.vis e e1) <==>
                                     (mem e l.l /\ mem e1 l.l /\ get_id e <> get_id e1 /\ l.vis e e1) \/
                                     (mem e a.l /\ mem e1 a.l /\ get_id e <> get_id e1 /\ a.vis e e1) \/
                                     (mem e l.l /\ mem e1 a.l /\ get_id e <> get_id e1))))
let union l a =
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1)) (union1 l a))

val absmerge1 : l:ae
              -> a:ae
              -> b:ae
              -> Pure (list o)
                (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                          (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                          (forall e. mem e l.l ==> not (member (get_id e) b.l)))
                (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique u))) (decreases %[l.l;a.l;b.l])
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
                         (forall e. mem e l.l ==> not (member (get_id e) b.l)))
               (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                               (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2) <==>
                                         (mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/
                                         (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ (union l a).vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ (union l b).vis e1 e2)) 
                               ))
#set-options "--z3rlimit 10000"
let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) ||
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1 && (union l a).vis o o1) ||
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1) && (union l b).vis o o1) (absmerge1 l a b))

val remove : l:s 
           -> ele:(nat * nat)
           -> Pure s 
             (requires (mem ele l))
             (ensures (fun res -> (forall e. mem e res <==> mem e l /\ e <> ele) /\
                               not (member_ele (snd ele) res) /\ not (member_id (fst ele) res) /\
                               (forall e. member_id e res <==> member_id e l /\  e <> fst ele) /\
                               (forall e. member_ele e res <==> member_ele e l /\ e <> snd ele)))
let rec remove l ele =
  match l with
  |[] -> []
  |x::xs -> if x = ele then xs else x::(remove xs ele)

val diff : a:s
          -> l:s
          -> Pure s
            (requires true)
            (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\
                            (forall e. mem e d /\ member_id (fst e) d <==> 
                                  mem e a /\ member_id (fst e) a /\ not (mem e l)) /\
                            (forall e. mem e d  /\ member_ele (snd e) d <==> 
                                      mem e a /\ member_ele (snd e) a /\ not (mem e l)) /\
                            (forall e. mem e a /\ mem e l ==> not (member_ele (snd e) d) /\ not (member_id (fst e) d))))
                            (decreases %[l;a])
#set-options "--z3rlimit 1000000"
let rec diff a l = 
  match a, l with
  |_,[] -> a
  |_,x::xs -> if (mem x a) then diff (remove a x) xs else diff a xs

val get_node : l:s 
             -> ele:nat
             -> Pure (nat * nat)
               (requires (member_ele ele l))
               (ensures (fun e -> mem e l /\ snd e = ele))
let rec get_node l ele =
  match l with
  |(id1,ele1)::xs -> if ele = ele1 then (id1,ele1) else get_node xs ele

val unionst : a:s
         -> b:s
         -> Pure s
           (requires (forall e. member_id e a ==> not (member_id e b)) /\
                     (forall e. member_ele e a ==> not (member_ele e b)))

           (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b) /\
                           (forall e. member_id e r <==> member_id e a \/ member_id e b) /\
                           (forall e. member_ele e r <==> member_ele e a \/ member_ele e b)))
let rec unionst a b =
    match a,b with
    |[],[] -> []
    |x::xs,_ -> x::unionst xs b
    |_ -> b

val lemma5 : a:s
           -> b:s
           -> Lemma (requires (forall e. member_id e a ==> not (member_id e b)))
                   (ensures (forall e e1. mem e a /\ not (member_ele (snd e) b) /\ mem e1 a /\ member_ele (snd e1) b ==>
                             fst e <> fst e1))
#set-options "--z3rlimit 100000000"
let rec lemma5 a b = 
      match a, b with
      |[],[] -> ()
      |x::xs,_ -> lemma5 xs b
      |[],_ -> ()

val merge1 : l:s
           -> a:s 
           -> b:s 
           -> Pure s
            (requires (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))) /\
                      (forall e. (mem e l /\ mem e a /\ mem e b) ==> 
                             not (member_ele (snd e) (diff a l)) /\ not (member_ele (snd e) (diff b l)) /\
                             not (member_id (fst e) (diff a l)) /\ not (member_id (fst e) (diff b l))) /\
                      (forall e. mem e (diff a l) /\ member_ele (snd e) (diff b l) ==> 
                            fst (get_node a (snd e)) <> fst (get_node b (snd e))) /\
                      (forall e. mem e (diff b l) /\ member_ele (snd e) (diff a l) ==> 
                            fst (get_node b (snd e)) <> fst (get_node a (snd e))))
           (ensures (fun res -> (forall e. member_ele e res ==> member_ele e a \/ member_ele e b) /\ 
                             (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                           (mem e (diff a l) /\ member_ele (snd e) (diff a l) /\ not (member_ele (snd e) (diff b l))) \/
                           (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ not (member_ele (snd e) (diff a l))) \/
                           (mem e (diff a l) /\ member_ele (snd e) (diff a l) /\ member_ele (snd e) (diff b l) /\
                           fst (get_node a (snd e)) > fst (get_node b (snd e))) \/
                           (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ member_ele (snd e) (diff a l) /\
                           fst (get_node b (snd e)) > fst (get_node a (snd e))))))
                              (decreases %[(length l); (length a); (length b)])

#set-options "--z3rlimit 100000000"
let merge1 l a b = 
  let i = filter (fun e -> mem e a && mem e b) l in
  assert (forall e. mem e i <==> mem e l /\ mem e a /\ mem e b);
  assert (forall e. member_ele e i ==> member_ele e l /\ member_ele e a /\ member_ele e b);
  let la = diff a l in let lb = diff b l in
  let la1 = filter (fun e -> member_ele (snd e) la && not (member_ele (snd e) lb)) la in
  let lb1 = filter (fun e -> member_ele (snd e) lb && not (member_ele (snd e) la)) lb in
  let la2 = filter (fun e -> member_ele (snd e) la && member_ele (snd e) lb && 
                          fst (get_node a (snd e)) > fst (get_node b (snd e))) la in
  let lb2 = filter (fun e -> member_ele (snd e) la && member_ele (snd e) lb && 
                          fst (get_node b (snd e)) > fst (get_node a (snd e))) lb in
  lemma5 la lb;
  assert (forall e. member_id e la1 ==> not (member_id e la2));
  lemma5 lb la;
  assert (forall e. member_id e lb1 ==> not (member_id e lb2));
  let u1 = unionst i la1 in
  let u2 = unionst u1 lb1 in
  let u3 = unionst u2 la2 in
  unionst u3 lb2
(*974501 ms*)

val merge : ltr: ae
          -> l:s 
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                               (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                               (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                               (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                               (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                               (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                               (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))))
                   (ensures (fun res -> (forall e. member_ele e res ==> member_ele e a \/ member_ele e b) /\ 
                               (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                             (mem e (diff a l) /\ member_ele (snd e) (diff a l) /\ not (member_ele (snd e) (diff b l))) \/
                             (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ not (member_ele (snd e) (diff a l))) \/
                             (mem e (diff a l) /\ member_ele (snd e) (diff a l) /\ member_ele (snd e) (diff b l) /\
                             fst (get_node a (snd e)) > fst (get_node b (snd e))) \/
                             (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ member_ele (snd e) (diff a l) /\
                             fst (get_node b (snd e)) > fst (get_node a (snd e))))))

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b = 
  assert (forall e. (mem e l /\ mem e a /\ mem e b) ==> 
              not (member_ele (snd e) (diff a l)) /\ not (member_ele (snd e) (diff b l)) /\
                                not (member_id (fst e) (diff a l)) /\ not (member_id (fst e) (diff b l)));
  assert (forall e. mem e (diff a l) /\ member_ele (snd e) (diff b l) ==> 
               fst (get_node a (snd e)) <> fst (get_node b (snd e)));
  assert (forall e. mem e (diff b l) /\ member_ele (snd e) (diff a l) ==> 
               fst (get_node b (snd e)) <> fst (get_node a (snd e))) ;
  merge1 l a b 

val lemma1 : ltr: ae
           -> l:s 
           -> atr:ae
           -> a:s 
           -> btr:ae
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                              (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                              (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                              (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))))
                   (ensures (forall e. (mem e (diff a l)) ==> (mem ((fst e), Add (snd e)) atr.l)) /\
                            (forall e. (mem e (diff b l)) ==> (mem ((fst e), Add (snd e)) btr.l)))

#set-options "--z3rlimit 10000000"
let lemma1 ltr l atr a btr b = ()
(*435894 ms*)

#set-options "--z3rlimit 10000000"
val lemma2 : ltr: ae
           -> l:s 
           -> atr:ae
           -> aa:s 
           -> btr:ae
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                               (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                               (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                               (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                               (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                               (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                               (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                   (ensures (forall a. mem a (absmerge ltr atr btr).l /\ opa a ==> 
                            (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r &&
                            get_id a <> get_id r ==> not ((absmerge ltr atr btr).vis a r)) ==>
                            member_ele (get_ele a) (merge ltr l atr aa btr b)))

#set-options "--z3rlimit 10000000"
let lemma2 ltr l atr a btr b = ()
(*144251 ms*)

val lemma3 : ltr:ae
           -> l:s
           -> atr:ae
           -> aa:s
           -> btr:ae
           -> b:s
             -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                  (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                     (ensures (forall e. mem e (merge ltr l atr aa btr b) ==> 
                                 (forall a. mem a (absmerge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
                                 (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r ==> 
                                 not (get_id a <> get_id r && (absmerge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000000"
let lemma3 ltr l atr a btr b = ()
(*211083 ms*)

val lemma4 : ltr:ae
           -> l:s
           -> atr:ae
           -> aa:s
           -> btr:ae
           -> b:s
             -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                  (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
             (ensures (forall e. mem e (merge ltr l atr aa btr b) ==> (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\
                      (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele r = snd e ==> 
                     not (fst e <> get_id r && (absmerge ltr atr btr).vis ((fst e), Add (snd e)) r)))))

#set-options "--z3rlimit 10000000"
let lemma4 ltr l atr a btr b = 
  lemma1 ltr l atr a btr b;
  ()

val prop_merge : ltr:ae
               -> l:s
               -> atr:ae
               -> a:s
               -> btr:ae
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                  (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))))
                     (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma2 ltr l atr a btr b;
  lemma3 ltr l atr a btr b;
  lemma4 ltr l atr a btr b;
  ()



(* assert ((forall e. member_id e i ==> not (member_id e la1)) /\ (forall e. member_ele e i ==> not (member_ele e la1)));
  assert ((forall e. member_id e i ==> not (member_id e lb1)) /\ (forall e. member_ele e i ==> not (member_ele e lb1)));
  assert ((forall e. member_id e i ==> not (member_id e la2)) /\ (forall e. member_ele e i ==> not (member_ele e la2)));
  assert ((forall e. member_id e i ==> not (member_id e lb2)) /\ (forall e. member_ele e i ==> not (member_ele e lb2)));
  
  assert ((forall e. member_id e la1 ==> not (member_id e lb1)) /\ (forall e. member_ele e la1 ==> not (member_ele e lb1)));
  assert ((forall e. member_id e la1 ==> not (member_id e la2)) /\ (forall e. member_ele e la1 ==> not (member_ele e la2)));
  assert ((forall e. member_id e la1 ==> not (member_id e lb2)) /\ (forall e. member_ele e la1 ==> not (member_ele e lb2)));

  assert ((forall e. member_id e lb1 ==> not (member_id e la2)) /\ (forall e. member_ele e lb1 ==> not (member_ele e la2)));
  assert ((forall e. member_id e lb1 ==> not (member_id e lb2)) /\ (forall e. member_ele e lb1 ==> not (member_ele e lb2)));

  assert ((forall e. member_id e la2 ==> not (member_id e lb2)) /\ (forall e. member_ele e la2 ==> not (member_ele e lb2)));*)
