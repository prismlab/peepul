module Orset_opt1

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

val member_ids : id:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_ids n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_ids n xs

val member_ele : ele:nat
               -> l:list (nat * nat)
               -> Tot (b:bool{(exists id. mem (id,ele) l) <==> b=true})
let rec member_ele ele l =
    match l with
    |[] -> false
    |(_,ele1)::xs -> (ele = ele1) || member_ele ele xs

val unique_s : l:list (nat * nat)
             -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_ids id xs) && unique_s xs

val unique_ele : l:list (nat * nat)
               -> Tot bool
let rec unique_ele l =
    match l with
    |[] -> true
    |(_,ele)::xs -> not (member_ele ele xs) && unique_ele xs

type s = l:list (nat (*unique id*)* nat (*ele*)) {unique_s l /\ unique_ele l}

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
               -> Lemma (requires (unique_s l /\ unique_ele l))
                       (ensures (unique_s (filter f l) /\ unique_ele (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val update : s1:s
           -> ele:nat
           -> id:nat
           -> Pure s
             (requires (member_ele ele s1) /\ not (member_ids id s1))
             (ensures (fun u -> (forall e. mem e s1 /\ snd e <> ele <==> mem e u /\ snd e <> ele) /\
                       (forall e. mem e u /\ fst e <> id /\ member_ids (fst e) u <==> mem e s1 /\ snd e <> ele /\ member_ids (fst e) s1) /\
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
             (requires (not (member_ids (get_id op) s1)))
             (ensures (fun res -> (opa op ==> (forall e. mem e s1 /\ snd e <> get_ele op <==> mem e res /\ snd e <> get_ele op) /\
                                          (forall e. mem e res /\ fst e <> get_id op /\ member_ids (fst e) res <==> mem e s1 /\ snd e <> get_ele op /\ member_ids (fst e) s1) /\
                                          (forall e. member_ele e s1 \/ e = get_ele op <==> member_ele e res) /\
                                          (forall e. mem e res /\ e <> ((get_id op), (get_ele op)) <==> mem e s1 /\ snd e <> get_ele op) /\
                                            mem ((get_id op), (get_ele op)) res) /\
                               (opr op ==> (forall e. mem e res <==> mem e s1 /\ snd e <> get_ele op))))
let app_op s1 op =
    if (opa op) 
      then (if member_ele (get_ele op) s1 then (update s1 (get_ele op) (get_id op)) else ((get_id op),(get_ele op))::s1) 
        else (if member_ele (get_ele op) s1 then (remove_ele s1 (get_ele op)) else s1)

val member_id : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists op. mem (id,op) l) <==> b=true})
let rec member_id n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_id n xs

val unique : l:list o
           -> Tot bool
let rec unique l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_id id xs) && unique xs

(*)noeq type ae =
  |A : vis : (o -> o -> Tot bool)
     -> l:(list o) {(unique l) /\
                   (forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ get_id e <> get_id e' /\ get_id e' <> get_id e'' /\ get_id e <> get_id e''  /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\
                   (forall e e'. (mem e l /\ mem e' l /\ get_id e <> get_id e' /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                   (forall e. mem e l ==> not (vis e e) (*irreflexive*))}
     -> ae*)

noeq type ae = 
     |A : vis:(o -> o -> Tot bool) -> l:list o {unique l} -> ae

assume val axiom : l:ae
                      -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\ 
                               get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*)/\ 
                               (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                               (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*)))
                               [SMTPat (unique l.l)]

val gt : a:nat -> b:nat {a <> b} -> Tot (b1:bool{(b1 = true <==> a > b) /\ (b1 = false <==> a < b)})
let gt a b = a > b
 
#set-options "--query_stats"
val sim : tr:ae
        -> s1:s 
          -> Tot (b:bool {b = true <==> (forall a. mem a s1 ==> (mem ((fst a), Add (snd a)) tr.l /\ 
       (forall r. mem r tr.l /\ opr r ==> not (fst a <> get_id r && snd a = get_ele r && tr.vis ((fst a), Add (snd a)) r)) /\
                (forall a1. mem a1 tr.l /\ opa a1 ==> 
                       not (fst a <> get_id a1 && snd a = get_ele a1 && tr.vis ((fst a), Add (snd a)) a1)))) /\

                (forall a. (mem a tr.l /\ opa a /\ (forall r. mem r tr.l /\ opr r ==>
                      not (get_id a <> get_id r && get_ele a = get_ele r && tr.vis a r))
                        ==>  member_ele (get_ele a) s1))})


#set-options "--z3rlimit 1000000"
let sim tr s1 = 
  let lsta = (filter (fun a -> opa a) tr.l) in
  let lstr = (filter (fun r -> opr r) tr.l) in
  let lst = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr) &&
                          not (existsb (fun a1 -> get_id a <> get_id a1 && get_ele a = get_ele a1 && tr.vis a a1) lsta)) lsta in
  let lst1 = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

  forallb (fun e ->  mem ((fst e), Add (snd e)) lst) s1 &&
  forallb (fun e -> member_ele (get_ele e) s1) lst1

(*)#set-options "--query_stats"
val sim : tr:ae
        -> s1:s 
          -> Tot (b:bool {b = true <==> (forall a. mem a s1 <==> (mem ((fst a), Add, (snd a)) tr.l /\ 
                        (forall r. mem r tr.l /\ get_op r = Rem ==>
                              not (fst a <> get_id r && snd a = get_ele r && tr.vis ((fst a), Add, (snd a)) r)) /\
                        (forall a1. mem a1 tr.l /\ get_op a1 = Add ==> 
                               not (fst a <> get_id a1 && snd a = get_ele a1 && tr.vis ((fst a), Add, (snd a)) a1)) /\
                        (forall a2. mem a2 tr.l /\ get_op a2 = Add  /\
                        (forall r. mem r tr.l /\ get_op r = Rem ==>
                              not (get_id a2 <> get_id r && get_ele a2 = get_ele r && tr.vis a2 r)) /\
                        (forall a1. mem a1 tr.l /\ get_op a1 = Add ==> 
                               not (get_id a2 <> get_id a1 && get_ele a2 = get_ele a1 && tr.vis a2 a1)) ==>
                               not (get_id a2 <> fst a && get_ele a2 = snd a && not (tr.vis a2 ((fst a), Add, (snd a)) || tr.vis ((fst a), Add, (snd a)) a2) && gt (get_id a2) (fst a)))))})


#set-options "--z3rlimit 1000000"
let sim tr s1 = 
  let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
  let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
  let lst = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr) &&
                          not (existsb (fun a1 -> get_id a <> get_id a1 && get_ele a = get_ele a1 && tr.vis a a1) lsta)) lsta in
  (*)let lst1 = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in*)
  let lst1 = filter (fun a -> not (existsb (fun a1 -> get_id a <> get_id a1 && get_ele a = get_ele a1 && not (tr.vis a a1 || tr.vis a1 a) && gt (get_id a1) (get_id a)) lst)) lst in

  forallb (fun e -> mem ((fst e), Add, (snd e)) lst1) s1 &&
  forallb (fun e -> mem ((get_id e), (get_ele e)) s1) lst1*)

val union1 : l:ae
           -> a:ae
           -> Pure (list o)
             (requires (forall e. (mem e l.l ==> not (member_id (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique u))) (decreases %[l.l;a.l])
let rec union1 l a =
  match l,a with
  |(A _ []), (A _ []) -> []
  |(A _ (x::xs)), _ -> x::(union1 (A l.vis xs) a)
  |(A _ []), (A _ (x::xs)) -> x::(union1 l (A a.vis xs))

val union : l:ae
          -> a:ae
          -> Pure ae
            (requires (forall e. (mem e l.l ==> not (member_id (get_id e) a.l))))
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
                (requires (forall e. mem e l.l ==> not (member_id (get_id e) a.l)) /\
                          (forall e. mem e a.l ==> not (member_id (get_id e) b.l)) /\
                          (forall e. mem e l.l ==> not (member_id (get_id e) b.l)))
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
               (requires (forall e. mem e l.l ==> not (member_id (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (member_id (get_id e) b.l)) /\
                         (forall e. mem e l.l ==> not (member_id (get_id e) b.l)))
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
                               not (member_ele (snd ele) res) /\ not (member_ids (fst ele) res) /\
                               (forall e. member_ids e res <==> member_ids e l /\  e <> fst ele) /\
                               (forall e. member_ele e res <==> member_ele e l /\ e <> snd ele)))
let rec remove l ele =
  match l with
  |[] -> []
  |x::xs -> if x = ele then xs else x::(remove xs ele)

val diff2 : a:s
          -> l:s
          -> Pure s
            (requires true)
            (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\
                            (forall e. mem e d /\ member_ids (fst e) d <==> 
                                  mem e a /\ member_ids (fst e) a /\ not (mem e l)) /\
                            (forall e. mem e d  /\ member_ele (snd e) d <==> 
                                      mem e a /\ member_ele (snd e) a /\ not (mem e l)) /\
                            (forall e. mem e a /\ mem e l ==> not (member_ele (snd e) d))))
                            (decreases %[l;a])
let rec diff2 a l = 
  match a, l with
  |_,[] -> a
  |_,x::xs -> if (mem x a) then diff2 (remove a x) xs else diff2 a xs

val get_node : l:s 
             -> ele:nat
             -> Pure (nat * nat)
               (requires (member_ele ele l))
               (ensures (fun e -> mem e l /\ snd e = ele))
let rec get_node l ele =
  match l with
  |(id1,ele1)::xs -> if ele = ele1 then (id1,ele1) else get_node xs ele

val lemma_vis : ltr:ae
             -> l:s
             -> atr:ae
             -> a:s 
             -> btr:ae
             -> b:s 
             -> Lemma
             (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                       (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                       (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                       (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
             (ensures (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ get_id e1 <> get_id e2 /\ not (ltr.vis e1 e2)) \/
                                (mem e1 atr.l /\ mem e2 atr.l /\ get_id e1 <> get_id e2 /\ not (atr.vis e1 e2)) \/
                                (mem e1 btr.l /\ mem e2 btr.l /\ get_id e1 <> get_id e2 /\ not (btr.vis e1 e2)) \/
                                (mem e1 atr.l /\ mem e2 btr.l /\ get_id e1 <> get_id e2) \/
                                (mem e1 btr.l /\ mem e2 atr.l /\ get_id e1 <> get_id e2) \/
                                (mem e1 atr.l /\ mem e2 ltr.l /\ get_id e1 <> get_id e2) \/
                                (mem e1 btr.l /\ mem e2 ltr.l /\ get_id e1 <> get_id e2)  <==>
                                (mem e1 (absmerge ltr atr btr).l /\ mem e2 (absmerge ltr atr btr).l /\ get_id e1 <> get_id e2 /\ 
                                               not ((absmerge ltr atr btr).vis e1 e2))) /\
                      (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ get_id e1 <> get_id e2 /\ not (ltr.vis e1 e2 || ltr.vis e2 e1)) \/
                                (mem e1 atr.l /\ mem e2 atr.l /\ get_id e1 <> get_id e2 /\ not (atr.vis e1 e2 || atr.vis e2 e1)) \/
                                (mem e1 btr.l /\ mem e2 btr.l /\ get_id e1 <> get_id e2 /\ not (btr.vis e1 e2 || btr.vis e2 e1)) \/
                                (mem e1 atr.l /\ mem e2 btr.l /\ get_id e1 <> get_id e2) \/
                                (mem e1 btr.l /\ mem e2 atr.l /\ get_id e1 <> get_id e2) <==>
                                (mem e1 (absmerge ltr atr btr).l /\ mem e2 (absmerge ltr atr btr).l /\ get_id e1 <> get_id e2 /\ not ((absmerge ltr atr btr).vis e1 e2 || (absmerge ltr atr btr).vis e2 e1))))
#set-options "--z3rlimit 1000000"
let lemma_vis ltr l atr a btr b = ()

val lemma1 : ltr:ae
              -> l:s
              -> atr:ae
              -> a:s 
              -> btr:ae
              -> b:s 
              -> Lemma
              (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                        (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                        (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                        (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
              (ensures (forall e. member_ids e (diff2 a l) ==> not (member_ids e (diff2 b l))))
#set-options "--z3rlimit 1000000"
let lemma1 ltr l atr a btr b =
  admit ()

val merge1 : l:s
           -> a:s 
           -> b:s 
           -> Pure s
            (requires (forall e. member_ids e (diff2 a l) ==> not (member_ids e (diff2 b l))) /\
                      (forall e. (mem e l /\ mem e a /\ mem e b) ==> 
                             not (member_ele (snd e) (diff2 a l)) /\ not (member_ele (snd e) (diff2 b l))))
            (ensures (fun res -> (forall e. member_ele e res <==> (member_ele e l /\ member_ele e a /\ member_ele e b) \/ 
                              (member_ele e (diff2 a l) \/ member_ele e (diff2 b l))) /\ 
                              (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/
                              (mem e (diff2 a l)) \/ (mem e (diff2 b l) /\ not (member_ele (snd e) (diff2 a l))))))
                              (decreases %[l;a;b])

#set-options "--z3rlimit 10000000"
let rec merge1 l a b = 
  match l,a,b with
        |[],[],[] -> []
        |x::xs,_,_ ->  if (mem x a && mem x b) then x::(merge1 xs (remove a x) (remove b x)) 
                        else if (mem x a) then (merge1 xs (remove a x) b)
                          else if (mem x b) then (merge1 xs a (remove b x))
                            else (merge1 xs a b)
        |_,_,(id,ele)::xs -> if (mem (id,ele) l) then merge1 (remove l (id,ele)) a xs
                              else if (not (member_ele ele a)) then (id,ele)::merge1 [] a xs
                                else merge1 [] a xs
        |[],_,[] -> a
        
  (*)match l,a,b with
        |[],[],[] -> []
        |x::xs,_,_ ->  if (mem x a && mem x b) then x::(merge1 xs (remove a x) (remove b x)) 
                       else if (mem x a) then (merge1 xs (remove a x) b)
                         else if (mem x b) then (merge1 xs a (remove b x))
                         else (merge1 xs a b)
        |[],(id,ele)::xs,_ -> if (not (member_ele ele b)) then (id,ele)::merge1 [] xs b 
                              else (if (member_ele ele b && id <> (fst (get_node b ele)) && gt id (fst (get_node b ele)))
                                then ((id,ele)::merge1 [] xs (remove b (get_node b ele)))
                                  else merge1 [] xs b)
        |[],[],x::xs -> b*)
        
  
 (*) match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ ->  if (mem x a && mem x b) then x::(merge1 xs (remove a x) (remove b x)) 
                  else if (mem x a) then (merge1 xs (remove a x) b)
                    else if (mem x b) then (merge1 xs a (remove b x))
                      else (merge1 xs a b)
  |[],(id,ele)::xs,_ -> if (not (member_ele ele b)) then (id,ele)::merge1 [] xs b 
                          else if (member_ele ele b) then ((id,ele)::merge1 [] xs (remove b (get_node b ele)))
                            else merge1 [] xs b
  |[],[],x::xs -> b*)

  (*)match l,a,b with
    |[],[],[] -> []
    |x::xs,_,_ ->  if (mem x a && mem x b) then x::(merge1 xs (remove a x) (remove b x)) 
                     else if (mem x a) then (merge1 xs (remove a x) b)
                       else if (mem x b) then (merge1 xs a (remove b x))
                        else (merge1 xs a b)
    |[],(id,ele)::xs,_ -> if (not (member_ele ele b)) then (id,ele)::merge1 [] xs b 
                            else (if (member_ele ele b && id <> (fst (get_node b ele)) && gt id (fst (get_node b ele)))
                               then ((id,ele)::merge1 [] xs (remove b (get_node b ele)))
                                 else merge1 [] xs b)
    |[],[],x::xs -> b*)
    (*pick the greater id from (a-l) and (b-l) *)

val merge : ltr: ae
          -> l:s 
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (fun res -> (forall e. member_ele e res <==> (member_ele e l /\ member_ele e a /\ member_ele e b) \/ 
                                     (member_ele e (diff2 a l) \/ member_ele e (diff2 b l))) /\ 
                                     (forall e. mem e res ==> (mem e l /\ mem e a /\ mem e b) \/ 
                                     (mem e (diff2 a l)) \/ (mem e (diff2 b l) /\ not (member_ele (snd e) (diff2 a l))))))
#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b = 
  lemma1 ltr l atr a btr b;
  merge1 l a b

val lemma2 : ltr: ae
           -> l:s 
           -> atr:ae
           -> a:s 
           -> btr:ae
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (forall e. (mem e l /\ mem e a /\ mem e b) ==> (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\ 
                            (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ fst e <> get_id r /\ snd e = get_ele r ==> 
                            not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) r)) /\
                            (forall a1. mem a1 (absmerge ltr atr btr).l /\ opa a1 /\ fst e <> get_id a1 /\ snd e = get_ele a1 ==>
                            not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) a1)))))

#set-options "--z3rlimit 10000000"
let lemma2 ltr l atr a btr b =
  lemma1 ltr l atr a btr b;
  lemma_vis ltr l atr a btr b;
  ()
(*174916*)

val lemma3 : ltr:ae
           -> l:s
           -> atr:ae
           -> a:s
           -> btr:ae
           -> b:s
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (forall e. (mem e (diff2 a l)) ==> (mem ((fst e), Add (snd e)) atr.l)) /\
                            (forall e. (mem e (diff2 b l)) ==> (mem ((fst e), Add (snd e)) btr.l)))

#set-options "--z3rlimit 10000000"
let lemma3 ltr l atr a btr b = 
  lemma1 ltr l atr a btr b;
  lemma_vis ltr l atr a btr b;
  let lsta = filter (fun a -> opa a) (union ltr atr).l in
  let lstr = filter (fun r -> opr r) (union ltr atr).l in
  let lst = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && (union ltr atr).vis a r) lstr) &&
                          not (existsb (fun a1 -> get_id a <> get_id a1 && get_ele a = get_ele a1 && (union ltr atr).vis a a1) lsta)) lsta in
  assert (forall e. mem e a ==> mem ((fst e), Add (snd e)) (union ltr atr).l); 
  assert (forall e. not (mem ((fst e), Add (snd e)) (union ltr atr).l) ==> not (mem e a));
  assert (forall e. mem e (diff2 a l) ==> not (mem e l));
  assert (forall e. mem e (diff2 a l) ==> mem ((fst e), Add (snd e)) lst);
  assert (forall e e1. mem e ltr.l /\ opa e /\ mem e1 atr.l /\ opr e1 /\ get_id e <> get_id e1 /\ get_ele e = get_ele e1 ==> not (mem ((get_id e), (get_ele e)) a));
  admit ()

val lemma4 : ltr:ae
           -> l:s 
           -> atr:ae
           -> a:s 
           -> btr:ae
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (forall e. mem e (absmerge ltr atr btr).l /\ opa e /\
                            (forall r. mem r (absmerge ltr atr btr).l /\ opr r ==> 
                                  not (get_id e <> get_id r && get_ele e = get_ele r && (absmerge ltr atr btr).vis e r))
                                 ==> member_ele (get_ele e) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let lemma4 ltr l atr a btr b = 
    lemma_vis ltr l atr a btr b;
    lemma1 ltr l atr a btr b;
    ()
(*3169 ms*)

val prop_merge : ltr:ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma_vis ltr l atr a btr b;
  lemma1 ltr l atr a btr b;
  lemma2 ltr l atr a btr b;
  lemma3 ltr l atr a btr b;
  lemma4 ltr l atr a btr b;
  ()
(*41180 ms*)

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member_id (get_id op) tr.l)))
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
                                (not (member_id (get_id op) tr.l)) )
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op =
  assert (not (member_ids (get_id op) st)); 
  ()
 (*45366 ms*)

val convergence : tr:ae
                  -> a:s
                  -> b:s  
                  -> Lemma (requires (sim tr a /\ sim tr b))
                          (ensures (forall e. member_ele e a <==> member_ele e b))
let convergence tr a b = ()
