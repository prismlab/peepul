module Orset_opt_detailed

open FStar.List.Tot

type op =
  |Add
  |Rem

type o = (int (*unique id*) * op * int (*element*))

let get_id (id,_,_) = id
let get_op (_,op,_) = op
let get_ele (_,_,ele) = ele

val member_s : id:int 
             -> l:list (int * int)
             -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_s n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_s n xs

val unique_s : l:list (int * int)
             -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_s id xs) && unique_s xs

type s = l:list (int (*unique id*) * int (*element*)) {unique_s l}

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

val filter_uni : f:((int * int) -> bool)
               -> l:list (int * int) 
               -> Lemma (requires (unique_s l))
                       (ensures (unique_s (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val app_op : s1:s
           -> op:o 
           -> Pure s
             (requires (not (member_s (get_id op) s1)))
             (ensures (fun res -> (get_op op = Add ==> (forall e. mem e s1 \/ e = ((get_id op), (get_ele op)) <==> mem e res)) /\
                               (get_op op = Rem ==> (forall e. mem e res <==> mem e s1 /\ snd e <> get_ele op))))
let rec app_op s1 (id, op, ele) =
          match op with
          |Add -> (id, ele)::s1
          |Rem -> filter (fun e -> snd e <> ele) s1

val member : id:int 
           -> l:list o
           -> Tot (b:bool{(exists op ele. mem (id,op,ele) l) <==> b=true})
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

noeq type ae =
  |A : vis : (o -> o -> Tot bool)
     -> l:(list o) {(unique l) /\
                   (forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ get_id e <> get_id e' /\ get_id e' <> get_id e'' /\ get_id e <> get_id e''  /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\
                   (forall e e'. (mem e l /\ mem e' l /\ get_id e <> get_id e' /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                   (forall e. mem e l ==> not (vis e e) (*irreflexive*))}
     -> ae

#set-options "--query_stats"
val sim : tr:ae
        -> s1:s 
        -> Tot (b:bool {b = true <==> (forall a. mem a s1 <==> (mem ((fst a), Add, (snd a)) tr.l /\
                                    (forall r. mem r tr.l /\ fst a <> get_id r /\ get_op r = Rem ==>
                                          not (snd a = get_ele r && (tr.vis ((fst a), Add, (snd a)) r)))))})
let sim tr s1 =
    let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
    let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
    let lst = except (fun a -> (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

    forallb (fun e -> mem ((get_id e), (get_ele e)) s1) lst &&
    forallb (fun e -> mem ((fst e), Add, (snd e)) lst) s1

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
                                         (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ (union l b).vis e1 e2))))
#set-options "--z3rlimit 10000"
let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) ||
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1 && (union l a).vis o o1) ||
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1) && (union l b).vis o o1) (absmerge1 l a b))

val diff2 : a:list (int * int)
          -> l:list (int * int)
          -> Pure (list (int * int))
            (requires (unique_s a /\ unique_s l))
            (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\ unique_s d )) (decreases %[l;a;l;a])
let rec diff2 a l = 
  filter (fun e -> not (mem e l)) a

val remove : l:s 
           -> ele:(int * int)
           -> Pure s 
               (requires true)
               (ensures (fun res -> (forall e. mem e res <==> mem e l /\ e <> ele)))
let rec remove l ele =
  filter (fun e -> e <> ele) l

val merge_s : l:s
           -> a:s 
           -> b:s 
           -> Pure s 
           (requires (forall e. mem e (diff2 a l) ==> not (member_s (fst e) b)) /\
                     (forall e. mem e (diff2 b l) ==> not (member_s (fst e) a)))
           (ensures (fun res -> (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                             (mem e (diff2 a l)) \/ (mem e (diff2 b l)))))    (decreases %[l;a;b])
#set-options "--z3rlimit 10000"
let rec merge_s l a b = 
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> if (mem x a && mem x b) then x::(merge_s xs (remove a x) (remove b x)) 
                 else if (mem x a) then (merge_s xs (remove a x) b)
                   else if (mem x b) then (merge_s xs a (remove b x))
                     else (merge_s xs a b)
  |[],x::xs,_ -> x::(merge_s [] xs b)
  |[],[],x::xs -> b

val merge : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s 
            (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                      (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                      (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                      (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
            (ensures (fun res -> (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                              (mem e (diff2 a l)) \/ (mem e (diff2 b l)))))

#set-options "--z3rlimit 1000000"
let merge ltr l atr a btr b = 
  merge_s l a b
(*17421 ms*)

val prop_merge : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
    assert (forall e. (mem e l /\ mem e a /\ mem e b) <==> (mem ((fst e), Add, (snd e)) ltr.l /\ 
           (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\ get_op r = Rem ==> 
           not (snd e = get_ele r && (absmerge ltr atr btr).vis ((fst e), Add, (snd e)) r))));

    assert (forall e. (mem e (diff2 a l)) <==> (mem ((fst e), Add, (snd e)) atr.l /\ (forall r. mem r atr.l /\ fst e <> get_id r /\
           get_op r = Rem ==> not (snd e = get_ele r && atr.vis ((fst e), Add, (snd e)) r))));

    assert (forall e. (mem e (diff2 b l)) <==> (mem ((fst e), Add, (snd e)) btr.l /\ (forall r. mem r btr.l /\ fst e <> get_id r /\
           get_op r = Rem ==> not (snd e = get_ele r && btr.vis ((fst e), Add, (snd e)) r))));

    assert (forall e. (mem ((fst e), Add, (snd e)) ltr.l /\ (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\
           get_op r = Rem ==> not (snd e = get_ele r && (absmerge ltr atr btr).vis ((fst e), Add, (snd e)) r))) \/ 
           (mem ((fst e), Add, (snd e)) atr.l /\ (forall r. mem r atr.l /\ fst e <> get_id r /\ 
           get_op r = Rem ==> not (snd e = get_ele r && atr.vis ((fst e), Add, (snd e)) r))) \/
           (mem ((fst e), Add, (snd e)) btr.l /\ (forall r. mem r btr.l /\ fst e <> get_id r /\ 
           get_op r = Rem ==> not (snd e = get_ele r && btr.vis ((fst e), Add, (snd e)) r))) <==>
           (mem ((fst e), Add, (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\ 
           get_op r = Rem ==> not (snd e = get_ele r && (absmerge ltr atr btr).vis ((fst e), Add, (snd e)) r))));

    assert (forall e. ((mem e l /\ mem e a /\ mem e b) \/ (mem e (diff2 a l)) \/ (mem e (diff2 b l))) <==> 
           (mem ((fst e), Add, (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\ 
           get_op r = Rem ==> not (snd e = get_ele r && (absmerge ltr atr btr).vis ((fst e), Add, (snd e)) r))));

    assert (forall e. (mem e (merge ltr l atr a btr b)) <==> 
           (mem ((fst e), Add, (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\ 
           get_op r = Rem ==> not (snd e = get_ele r && (absmerge ltr atr btr).vis ((fst e), Add, (snd e)) r))));
    ()
(*15400 ms*)

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
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op = 
  assert (not (member_s (get_id op) st)); 
  ()
(*6140 ms*)

val convergence : tr:ae
                -> a:s
                -> b:s  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. mem e a <==> mem e b))
let convergence tr a b = ()
