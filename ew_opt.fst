module Ew_opt

open FStar.List.Tot

type op =
  |Enable 
  |Disable

type o = (nat (*timestamp*) * op)

val get_id : o -> nat
let get_id (id,_) = id

val get_op : o -> op
let get_op (_,op) = op

(*state = enable <==> state > 0; state = disable <==> state = 0*)
type s = nat (*timestamp*) 

val disable : s
let disable = 0
  
val app_op : s1:s -> op:o -> Tot (s2:s {(get_op op = Enable ==> s2 = get_id op) /\
                                      (get_op op = Disable ==> s2 = disable)})
let app_op t op =
  match get_op op with
  |Enable -> get_id op
  |Disable -> disable

val member_id : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists op. mem (id,op) l) <==> b=true})
let rec member_id n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_id n xs

val unique_id : l:list o
           -> Tot bool
let rec unique_id l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_id id xs) && unique_id xs

noeq type ae = 
  |A : vis:(o -> o -> Tot bool) -> l:list o {unique_id l} -> ae

assume val axiom : l:ae
                 -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\ 
          get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*)/\ 
                          (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> 
                                   not (l.vis e' e)) (*asymmetric*) /\
                          (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*)))
                          [SMTPat (unique_id l.l)]

val filter : #a:eqtype
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ f e})
let rec filter #a f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl
       
val filter_uni : f:(o -> bool)
               -> l:list o
               -> Lemma (requires (unique_id l))
                       (ensures (unique_id (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val existsb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a 
            -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true})
let rec existsb #a f l =
  match l with
  |[] -> false
  |hd::tl -> if f hd then true else existsb f tl

val gt : l:list o
       -> init:nat
       -> Pure nat
         (requires (forall e. mem e l ==> get_op e = Enable) /\ unique_id l)
         (ensures (fun r -> (mem (r, Enable) l \/ r = init) /\
                         (forall e. mem e l ==> r >= get_id e) /\ (r >= init)))
         (decreases (length l))
#set-options "--z3rlimit 10000"
let rec gt l init =
  match l with
  |[] -> init
  |(t, Enable)::xs -> if t > init then (gt xs t) else (gt xs init)

val sim : tr:ae
        -> s1:s
        -> Tot (b:bool {b = true <==> (s1 = gt (filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && tr.vis a r) (filter (fun r -> get_op r = Disable) tr.l))) (filter (fun a -> get_op a = Enable) tr.l)) disable)})

let sim tr s1 = 
  let lsta = filter (fun a -> get_op a = Enable) tr.l in
  let lstr = filter (fun r -> get_op r = Disable) tr.l in
  let lst = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && tr.vis a r) lstr)) lsta in 
  s1 = gt lst disable

val union1 : l:ae 
           -> a:ae
           -> Pure (list o)
             (requires (forall e. (mem e l.l ==> not (member_id (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique_id u))) (decreases %[l.l;a.l])
#set-options "--z3rlimit 10000"
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
                (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique_id u))) (decreases %[l.l;a.l;b.l])
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
                                         (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ (union l b).vis e1 e2))))
#set-options "--z3rlimit 10000"
let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1 && (union l a).vis o o1) || 
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1 && (union l b).vis o o1)) (absmerge1 l a b))

val merge : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                             (forall e. mem e (absmerge ltr atr btr).l ==> get_id e > 0) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1))
                   (ensures (fun res -> (res = a \/ res = b) /\
                                     (res = a <==> (l = a /\ l = b) \/
                                                  (l <> a /\ l <> b /\ a >= b) \/
                                                  (l = b /\ l <> a)) /\
                                     (res = l <==> l = a /\ l = b) /\
                                     (res = b <==> (l = a /\ l = b) \/
                                                     (l <> a /\ l <> b /\ b >= a) \/
                                                     (l = a /\ l <> b)) /\
                                    
                                     (res = disable <==> (l = a /\ b = disable) \/
                                                     (l = b /\ a = disable) \/
                                                     (a = disable /\ b = disable)) /\
                                     (res <> disable <==> (a <> disable /\ b <> disable) \/
                                                     (a <> disable /\ b = disable /\ l <> a) \/
                                                     (b <> disable /\ a = disable /\ l <> b))))
                                      
#set-options "--z3rlimit 100000"
let merge ltr l atr a btr b = 
 if (l = a && l = b) then l
   else if (l <> a && l <> b) then (if a >= b then a else b)
     else if (l = a) then b
       else a

val lemma : tr:ae
            -> s1:s
            -> Lemma (requires (forall e. mem e tr.l ==> get_id e > 0))
                    (ensures (sim tr s1) <==> ((mem (s1, Enable) tr.l /\ (forall r. mem r tr.l /\ get_op r = Disable ==>
                             not (s1 <> get_id r && tr.vis (s1, Enable) r))) \/ s1 = disable) /\
                             (forall a. (mem a tr.l /\ get_op a = Enable /\ (forall r. mem r tr.l /\ get_op r = Disable ==>
                                   not (get_id a <> get_id r && tr.vis a r))) ==> s1 >= get_id a) /\ s1 >= disable)
              (*[SMTPat (sim tr s1)]*)
              
#set-options "--z3rlimit 1000000"
let lemma tr s1 = ()
 
val lemma1 : ltr: ae
                -> l:s 
                -> atr:ae
                -> a:s 
                -> btr:ae
                -> b:s 
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                  (forall e. mem e (absmerge ltr atr btr).l ==> get_id e > 0) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1))
                        (ensures ((merge ltr l atr a btr b) >= disable))
let lemma1 ltr l atr a btr b = () 

val lemma2 : ltr: ae
                -> l:s 
                -> atr:ae
                -> a:s 
                -> btr:ae
                -> b:s 
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                  (forall e. mem e (absmerge ltr atr btr).l ==> get_id e > 0) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1))
                         (ensures (forall e. (mem e (absmerge ltr atr btr).l /\ get_op e = Enable /\
                                  (forall r. mem r (absmerge ltr atr btr).l /\ get_op r = Disable ==>
                                        not (get_id e <> get_id r && (absmerge ltr atr btr).vis e r))) ==>
                                        (merge ltr l atr a btr b) >= get_id e))
let lemma2 ltr l atr a btr b = () 

#set-options "--query_stats"
val lemma3 : ltr: ae
                -> l:s 
                -> atr:ae
                -> a:s 
                -> btr:ae
                -> b:s 
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                  (forall e. mem e (absmerge ltr atr btr).l ==> get_id e > 0) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1))
                        (ensures ((mem ((merge ltr l atr a btr b), Enable) (absmerge ltr atr btr).l /\ 
                                 (forall r. mem r (absmerge ltr atr btr).l /\ get_op r = Disable ==>
                                      not ((merge ltr l atr a btr b) <> get_id r && (absmerge ltr atr btr).vis
                                      ((merge ltr l atr a btr b), Enable) r))) \/ (merge ltr l atr a btr b) = disable))
#set-options "--z3rlimit 10000000"
let lemma3 ltr l atr a btr b =  ()                         
(*131337 ms*)

val prop_merge : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member_id (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member_id (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member_id (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                 (forall e. mem e (absmerge ltr atr btr).l ==> get_id e > 0) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))
#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
lemma1 ltr l atr a btr b;
lemma2 ltr l atr a btr b;
lemma3 ltr l atr a btr b;
lemma (absmerge ltr atr btr) (merge ltr l atr a btr b);
()

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
                                (not (member_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e > 0) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op))
                      (ensures (sim (append tr op) (app_op st op)))
#set-options "--z3rlimit 10000000"
let prop_oper tr st op = ()

val convergence : tr:ae
                -> a:s
                -> b:s  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (a = b))
let convergence tr a b = ()
