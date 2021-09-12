module Lww

open FStar.List.Tot

type op =
  |Write : nat (*value*) -> op

type o = (nat (*timestamp*) * op)

let get_id (id,_) = id
let get_op (_,op) = op
let get_ele (_,Write n) = n

type s = (nat (*timestamp*) * nat (*value*))

val app_op : s1:s -> op:o -> Tot (s2:s {s2 = ((get_id op), (get_ele op))})
let app_op (t, v) (t1, Write v1) = (t1, v1)

val member : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists op. mem (id,op) l) <==> b=true})
let rec member n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member n xs

val mem_val : v:nat 
            -> l:list o
            -> Tot (b:bool{(exists id. mem (id, Write v) l) <==> b=true})
let rec mem_val n l =
  match l with
  |[] -> false
  |(_, Write v)::xs -> (n = v) || mem_val n xs

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

val init : s
let init = (0,0)

val gt : l:list o
       -> init1:(nat * nat)
       -> Pure (nat * nat)
         (requires true)
         (ensures (fun r -> (mem ((fst r), Write (snd r)) l \/ r = init1) /\
                         (forall e. mem e l ==> fst r >= get_id e) /\ (fst r >= fst init1)))
         (decreases (length l))
#set-options "--z3rlimit 10000"
let rec gt l init1 =
  match l with
  |[] -> init1
  |(t, Write n)::xs -> if t > fst init1 then (gt xs (t,n)) else (gt xs init1)

val find : l:list o
         -> id:nat
         -> Pure nat
           (requires (unique l) /\ member id l /\ id > 0)
           (ensures (fun v -> (mem (id, Write v) l) /\ mem_val v l))
let rec find l id =
  match l with
  |(id1, Write v)::xs -> if id = id1 then v else find xs id

#set-options "--query_stats"
val sim : tr:ae
        -> s1:s
        -> Tot (b:bool {b = true <==> s1 = gt tr.l init} )
let sim tr s1 = 
  s1 = gt tr.l init

val union1 : l:ae 
           -> a:ae
           -> Pure (list o)
             (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique u))) (decreases %[l.l;a.l])
#set-options "--z3rlimit 10000"
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
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1 && (union l b).vis o o1)) (absmerge1 l a b))

val merge : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                             (forall e. mem e (absmerge ltr atr btr).l ==> get_id e > 0))
                    (ensures (fun res -> ((fst a >= fst b) ==> res = a) /\
                                      ((fst b > fst a) ==> res = b) /\
                                      (fst res >= fst a /\ fst res >= fst b /\ fst res >= fst l) /\
                                      (res = a \/ res = b)))
#set-options "--z3rlimit 10000"
let merge ltr l atr a btr b = 
  assert ((fst a = fst b) ==> (fst l = fst a) /\ (fst l = fst b));
  if (fst a >= fst b) then a else b

val lemma : l:list o
          -> Lemma (requires unique l)
                  (ensures (forall ele. member (fst ele) l /\ (fst ele > 0) ==> 
                           (mem (fst ele, Write (snd ele)) l) ==> (snd ele = find l (fst ele))))
                  (decreases (length l))
let rec lemma l = 
  match l with
  |[] -> ()
  |x::xs -> lemma xs 

val prop_merge : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b)  /\
                                 (forall e. mem e (absmerge ltr atr btr).l ==> get_id e > 0))
                        (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma (absmerge ltr atr btr).l;
  ()

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
                                (get_id op > 0) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op))
                      (ensures (sim (append tr op) (app_op st op)))
let prop_oper tr st op = ()

val convergence : tr:ae
                -> a:s
                -> b:s  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures a = b)
let convergence tr a b = ()

