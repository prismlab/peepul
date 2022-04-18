module Map_gset
open FStar.List.Tot

open Library
module C = Gset

type op = (nat (*key*) * C.op)

val get_key : op1:(nat * op) -> Tot (k:nat {exists id v. op1 = (id, (k, C.Add v))})
let get_key (id, (k, C.Add v)) = k

val get_set : op1:(nat * op) -> Tot (s:C.op {exists id k. op1 = (id, (k, s))})
let get_set (id, (k, s)) = s

val get_val : op1:(nat * op) -> Tot (v:nat {exists id k. op1 = (id, (k, C.Add v))})
let get_val (id, (k, C.Add v)) = v

val get_key_s : s:(nat * C.s) -> Tot (s1:nat {(exists c. s = (s1,c))})
let get_key_s (k, _) = k

val mem_key_s : ele1:nat
             -> l:list (nat * C.s)
             -> Tot (b:bool {b=true <==> (exists c. mem (ele1,c) l) /\ (exists e. mem e l /\ get_key_s e = ele1)})
let rec mem_key_s ele1 l =
  match l with
  |[] -> false
  |x::xs -> get_key_s x = ele1 || mem_key_s ele1 xs

val unique_key : list (nat * C.s) -> bool
let rec unique_key l =
  match l with
  |[] -> true
  |(ele,_)::xs -> not (mem_key_s ele xs) && unique_key xs

val get_val_s1 : s:(nat * C.s) -> Tot (c:C.s {(exists i. s = (i,c))})
let get_val_s1 (_, c) = c

type s = l:list (nat * C.s) {unique_key l}

val get_val_s : i:nat -> s1:s -> Tot (c:C.s {(mem_key_s i s1 ==> mem (i,c) s1 /\ (exists e. mem e s1 ==> e = (i,c))) /\ 
                                         (not (mem_key_s i s1) ==> c = [])})
let rec get_val_s i s1 =
  match s1 with
  |[] -> []
  |x::xs -> if get_key_s x = i then (get_val_s1 x) else get_val_s i xs

val lemma2 : s1:s 
           -> Lemma (requires true)
                   (ensures (forall e. mem e s1 ==> (get_val_s (get_key_s e) s1 = get_val_s1 e)) /\
                            (forall e. mem e s1 ==> C.unique_s (get_val_s (get_key_s e) s1)))
                [SMTPat (unique_key s1)]
#set-options "--z3rlimit 10000000"
let rec lemma2  s1 = 
  match s1 with
  |[] -> ()
  |x::xs -> lemma2 xs 

val mem_op : ele1:op
           -> l:list (nat * op)
           -> Tot (b:bool {b=true <==> (exists id. mem (id, ele1) l) })
let rec mem_op ele2 l =
  match l with
  |[] -> false
  |(_, ele1)::xs -> ele1 = ele2 || mem_op ele2 xs

val mem_key : i:nat -> l:list (nat * op) -> Tot (b:bool {b=true <==> (exists id op. mem (id, (i, op)) l)})
let rec mem_key ele2 l =
  match l with
  |[] -> false
  |(_, (ele1, _))::xs -> ele1 = ele2 || mem_key ele2 xs

val filter_uni : #op:eqtype 
               -> f:((nat * op) -> bool)
               -> l:list (nat * op) 
               -> Lemma (requires (unique_id l ))
                       (ensures (unique_id (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni #op f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val project_op : o1:(nat * op)
               -> Tot (o2:(nat * C.op) {o2 = (get_id o1, get_set o1)})
let project_op op =
  match op with
  |(id, (k, set)) -> (id, set)

val project1 : i:nat
             -> l:ae op
             -> Pure (list (nat * C.op))
                    (requires true)
                    (ensures (fun r -> (forall id. mem_id id r <==> mem_id id l.l /\ 
                                    get_op (get_eve id l.l) = (i, (C.Add (get_val (get_eve id l.l))))) /\
                                  (forall id. mem_id id r <==> (mem_id id l.l /\ get_key (get_eve id l.l) = i)) /\ 
                                     unique_id r /\
                (forall e. mem e r <==> (mem ((get_id e), (i, C.Add (C.get_ele e))) l.l)) /\
                (forall e. mem e l.l /\ get_key e = i ==> mem (project_op e) r)))
            (decreases List.Tot.length l.l)

#set-options "--z3rlimit 10000000"
let rec project1 i l =
  match l.l with
  |[] -> []
  |x::xs -> if (get_key x = i) then (project_op x)::project1 i (A l.vis xs) else (project1 i (A l.vis xs))

val project : i:nat
            -> l:ae op
            -> Pure (ae C.op)
                   (requires true)
                   (ensures (fun r -> (forall id. mem_id id r.l <==> mem_id id l.l /\ 
                                   get_op (get_eve id l.l) = (i, (C.Add (get_val (get_eve id l.l))))) /\
              (forall id. mem_id id r.l <==> (mem_id id l.l /\ get_key (get_eve id l.l) = i)) /\ unique_id r.l /\
                 (forall e. mem e r.l <==> (mem ((get_id e), (i, C.Add (C.get_ele e))) l.l)) /\
                 (forall e. mem e l.l /\ get_key e = i ==> mem (project_op e) r.l) /\
                 (forall e e1. (get_id e <> get_id e1 /\ mem (get_id e, (i, C.Add (C.get_ele e))) l.l /\ 
              mem (get_id e1, (i, C.Add (C.get_ele e1))) l.l /\
                  l.vis (get_id e, (i, C.Add (C.get_ele e))) (get_id e1, (i, C.Add (C.get_ele e1)))) <==> 
            (get_id e <> get_id e1 /\ mem e r.l /\ mem e1 r.l /\ r.vis e e1))))
               (decreases length l.l)

#set-options "--z3rlimit 10000000"
let project i l =
  (A (fun o o1 -> (mem (get_id o, (i, C.Add (C.get_ele o))) l.l && mem (get_id o1, (i, C.Add (C.get_ele o1))) l.l &&  get_id o <> get_id o1 && l.vis (get_id o, (i, C.Add (C.get_ele o))) (get_id o1, (i, C.Add (C.get_ele o1))))) (project1 i l))

let pre_cond_op s1 op = true

val app_op : st:s -> op1:(nat * op)
           -> Pure s 
             (requires true)
             (ensures (fun r -> (forall ch. mem_key_s ch r <==> mem_key_s ch st \/ ch = get_key op1) /\
                             (forall e. mem e (get_val_s (get_key op1) r) <==> 
                                   mem e (get_val_s (get_key op1) st) \/ e = (get_val op1)) /\
                             (forall ch. mem_key_s ch st /\ ch <> (get_key op1) ==> 
                                    (forall e. mem e (get_val_s ch st) <==> mem e (get_val_s ch r)))))

#set-options "--z3rlimit 10000000"
let rec app_op st op1 =
  match st with
  |[] -> [(get_key op1, [get_val op1])]
  |(ch, x)::xs -> if ch = get_key op1 then (ch, (C.app_op x (project_op op1)))::xs
                     else (ch, x)::app_op xs op1

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {(b = true) <==> (forall ch. mem_key_s ch s1 <==> mem_key ch tr.l) /\
                                     (forall ch. mem_key_s ch s1 ==> C.sim (project ch tr) (get_val_s ch s1)) /\
                                     (forall e. mem e tr.l ==> (exists e1. mem e1 s1 /\ get_key e = get_key_s e1 /\
                                           mem (get_val e) (get_val_s1 e1)))})

#set-options "--z3rlimit 10000000"
let sim tr s1 = 
  forallb (fun e -> mem_key (get_key_s e) tr.l) s1 &&
  forallb (fun e -> mem_key_s (get_key e) s1) tr.l &&
  forallb (fun e -> C.sim (project (get_key_s e) tr) (get_val_s (get_key_s e) s1)) s1 &&
  forallb (fun e -> (existsb (fun e1 -> get_key e = get_key_s e1 && mem (get_val e) (get_val_s1 e1)) s1)) tr.l

val lemma4 : tr:ae op -> s1:s
           -> Lemma (requires sim tr s1)
                   (ensures (forall i. (C.sim (project i tr) (get_val_s i s1))))
                      [SMTPat (sim tr s1)]
let lemma4 tr s1 = ()

val convergence1 : tr:ae op
                 -> a:s
                 -> b:s
                 -> Lemma (requires (sim tr a /\ sim tr b))
                         (ensures (forall e. mem_key_s e a <==> mem_key_s e b))
#set-options "--z3rlimit 100000000"
let convergence1 tr a b = ()

val unique_keys : list nat -> Tot bool
let rec unique_keys l =
  match l with
  |[] -> true
  |x::xs -> not (mem x xs) && unique_keys xs

val get_lst : m:s -> Pure (list nat)
                    (requires true)
                    (ensures (fun r -> (forall i. mem i r <==> mem_key_s i m) /\ unique_keys r))
let rec get_lst m =
  match m with
  |[] -> []
  |(i,x)::xs -> i::get_lst xs

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall ch. mem_key_s ch a <==> mem_key_s ch b) /\
                                 (forall ch. mem_key_s ch a /\ mem_key_s ch b ==>
                                 (forall e. mem e (get_val_s ch a) <==> mem e (get_val_s ch b))))

#set-options "--z3rlimit 10000000"
let convergence tr a b =
  convergence1 tr a b

val lem_oper : tr:ae op 
             -> op:(nat * op)
             -> Lemma (requires (not (mem_id (get_id op) tr.l)))
                     (ensures (forall e. mem e (project (get_key op) (append tr op)).l <==> 
                                    mem e (append (project (get_key op) tr) (project_op op)).l) /\
               (forall e e1. mem e (project (get_key op) (append tr op)).l /\
                        mem e1 (project (get_key op) (append tr op)).l /\ (get_id e <> get_id e1) /\
                        (project (get_key op) (append tr op)).vis e e1  <==> 
                        mem e (append (project (get_key op) tr) (project_op op)).l /\
                    mem e1 (append (project (get_key op) tr) (project_op op)).l /\ get_id e <> get_id e1 /\
                        (append (project (get_key op) tr) (project_op op)).vis e e1) /\
         (forall i. i <> (get_key op) ==> (forall e. mem e (project i (append tr op)).l <==> mem e (project i tr).l) /\
         (forall e e1. mem e (project i (append tr op)).l /\ mem e1 (project i (append tr op)).l /\ get_id e <> get_id e1 /\
                    (project i (append tr op)).vis e e1 <==> 
        mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1)))

#set-options "--z3rlimit 10000000"
let lem_oper tr op = ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op) 
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op = 
  lem_oper tr op;
  assert (forall ch. mem_key_s ch (app_op st op) <==> mem_key ch (append tr op).l); 
  C.prop_oper (project (get_key op) tr) (get_val_s (get_key op) st) (project_op op); 
  assert (C.sim (project (get_key op) (append tr op)) (get_val_s (get_key op) (app_op st op)));
  assert (forall e. mem e (append tr op).l ==> (exists e1. mem e1 (app_op st op) /\ get_key e = get_key_s e1 /\
                                            mem (get_val e) (get_val_s1 e1)));
  ()

val get_key_lst : l:s -> a:s -> b:s
                -> Pure (list nat)
                  (requires (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b))
                  (ensures (fun r -> (forall i. mem i r <==> mem_key_s i a \/ mem_key_s i b) /\ unique_keys r))
                  (decreases %[l;a;b])

let rec get_key_lst l a b =
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> get_key_lst xs a b
  |[],x::xs,_ -> if (mem_key_s (get_key_s x) b) then get_key_lst [] xs b else (get_key_s x)::(get_key_lst [] xs b)
  |[],[],x::xs -> (get_key_s x)::(get_key_lst [] [] xs)

val merge1 : l:s
           -> a:s
           -> b:s
           -> lst:list nat 
           -> Pure s
            (requires (forall e. mem_key_s e l ==> mem_key_s e a /\ mem_key_s e b) /\ unique_keys lst /\
                      (forall ch. mem ch lst ==> (forall e. mem e (get_val_s ch l) ==>
                                        mem e (get_val_s ch a) /\ mem e (get_val_s ch b))))
            (ensures (fun r -> (forall ch. mem_key_s ch r <==> mem ch lst) /\
                        (forall ch. mem ch lst ==> (get_val_s ch r) =
                                   (C.merge1 (get_val_s ch l) (get_val_s ch a) (get_val_s ch b))) /\
                        (forall ch. mem ch lst ==> (forall e. mem e (get_val_s ch r) <==>
                                     mem e (C.merge1 (get_val_s ch l) (get_val_s ch a) (get_val_s ch b))))))
            (decreases lst)

#set-options "--z3rlimit 10000000" 
let rec merge1 l a b lst =
  match lst with
  |[] -> []
  |x::xs -> (x, C.merge1 (get_val_s x l) (get_val_s x a) (get_val_s x b))::merge1 l a b xs

val lem_merge1 : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> lst:list nat
               -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                 (forall ch. mem ch lst <==> mem_key_s ch a \/ mem_key_s ch b) /\ unique_keys lst)
                       (ensures (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b) /\
                                (forall ch. mem ch lst ==> (forall e. mem e (get_val_s ch l) ==>
                                       mem e (get_val_s ch a) /\ mem e (get_val_s ch b))))

#set-options "--z3rlimit 10000000"
let lem_merge1 ltr l atr a btr b lst = ()

let pre_cond_merge ltr l atr a btr b = true

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                 (ensures (fun r -> (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b) /\
                                 (forall i. mem_key_s i r <==> mem_key_s i a \/ mem_key_s i b) /\
                 (forall ch. mem_key_s ch r ==> 
                 (forall e. mem e (get_val_s ch l) ==> mem e (get_val_s ch a) /\ mem e (get_val_s ch b))) /\
                               (forall ch. mem_key_s ch r ==> (get_val_s ch r) =
                               (C.merge1 (get_val_s ch l) (get_val_s ch a) (get_val_s ch b))) /\
                             (forall ch. mem_key_s ch r ==> (forall e. mem e (get_val_s ch r) <==>
                                        mem e (C.merge1 (get_val_s ch l) (get_val_s ch a) (get_val_s ch b))))))

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b =
  let keys = get_key_lst l a b in
  lem_merge1 ltr l atr a btr b keys;
  let r = merge1 l a b keys in
  r

val remove_op1 : tr:ae C.op 
               -> x:(nat * C.op) 
               -> Pure (list (nat * C.op))
                      (requires (mem x tr.l))
                      (ensures (fun r -> (forall e. mem e r <==> mem e tr.l /\ e <> x) /\ unique r /\ 
                                      (List.Tot.length r = List.Tot.length tr.l - 1)))
                      (decreases tr.l)

let rec remove_op1 tr x =
  match tr.l with
  |x1::xs -> if x = x1 then xs else x1::remove_op1 (A tr.vis xs) x

val remove_op : tr:ae C.op 
              -> x:(nat * C.op) 
              -> Pure (ae C.op)
                     (requires (mem x tr.l))
                     (ensures (fun r -> (forall e. mem e r.l <==> mem e tr.l /\ e <> x) /\ unique r.l /\
                     (forall e e1. mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ e <> x /\ e1 <> x /\ tr.vis e e1 <==>
                    mem e (remove_op1 tr x) /\ mem e1 (remove_op1 tr x) /\ get_id e <> get_id e1 /\ tr.vis e e1) /\
                                (List.Tot.length r.l = List.Tot.length tr.l - 1)))
                    (decreases tr.l)
let remove_op  tr x =
    (A (fun o o1 -> mem o (remove_op1 tr x) && mem o1 (remove_op1 tr x) && get_id o <> get_id o1 && tr.vis o o1) (remove_op1 tr x))

val lemma6 : l:ae op 
           -> a:ae op 
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                   (ensures (forall e. mem_op e (union1 l a) <==> mem_op e l.l \/ mem_op e a.l))
                   (decreases %[l.l;a.l])

#set-options "--z3rlimit 10000000"
let rec lemma6 l a = 
  match l,a with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma6 (A l.vis xs) a
  |(A _ []), (A _ (x::xs)) -> lemma6 l (A a.vis xs)

val lemma61 : l:ae op
            -> a:ae op
            -> b:ae op
                 -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                                   (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                                   (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))
                         (ensures (forall e. mem_op e (absmerge1 l a b) <==> 
                                        mem_op e l.l \/ mem_op e a.l \/ mem_op e b.l))
                         (decreases %[l.l;a.l;b.l])

#set-options "--z3rlimit 10000000"
let rec lemma61 l a b = 
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma61 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma61 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma61 l a (A b.vis xs)

val remove_ele1 : ele:nat 
                -> l:(ae C.op) 
                -> Tot (l1:list (nat * C.op) {(forall e. mem e l1 <==> mem e l.l /\ C.get_ele e <> ele) /\ unique l1})
                  (decreases l.l)

let rec remove_ele1 k l =
  match l.l with
  |[] -> []
  |(id, (C.Add k1))::xs -> if k = k1 then remove_ele1 k (A l.vis xs) else (id, (C.Add k1))::remove_ele1 k (A l.vis xs)

val remove_ele : ele:nat 
               -> l:(ae C.op) 
               -> Tot (l1:(ae C.op) {(forall e. mem e l1.l <==> mem e l.l /\ C.get_ele e <> ele) /\
                                   (forall e e1. mem e l.l /\ mem e1 l.l /\ C.get_ele e <> ele /\ C.get_ele e1 <> ele /\
                                   get_id e <> get_id e1 /\ l.vis e e1 <==>
                 mem e (remove_ele1 ele l) /\ mem e1 (remove_ele1 ele l) /\ get_id e <> get_id e1 /\ l1.vis e e1)})
                  (decreases l.l)
let remove_ele x tr =
  (A (fun o o1 -> mem o (remove_ele1 x tr) && mem o1 (remove_ele1 x tr) && get_id o <> get_id o1 && tr.vis o o1) (remove_ele1 x tr))

val remove_st : ele:nat 
              -> s1:C.s {mem ele s1}
              -> Tot (s2:C.s {forall e. mem e s2 <==> mem e s1 /\ e <> ele})
let rec remove_st ele s1 =
  match s1 with
  |x::xs -> if x = ele then xs else x::remove_st ele xs

val lemma7 : tr:ae C.op -> s1:C.s -> tr1:ae C.op
           -> Lemma (requires C.sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                             (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                      mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                   (ensures (C.sim tr1 s1))
                   (decreases %[tr.l;s1;tr1.l])

#set-options "--z3rlimit 10000000"
let rec lemma7 tr s1 tr1 = 
  match tr.l, tr1.l with
  |[], [] -> ()
  |(id, (C.Add v))::xs, _ -> 
               if (C.mem_ele v xs) then lemma7 (remove_op tr (id, (C.Add v))) s1 (remove_op tr (id, (C.Add v)))
                      else lemma7 (remove_op tr (id, (C.Add v))) (remove_st v s1) (remove_op tr (id, (C.Add v)))
  |[], (_, (C.Add v))::xs -> ()

val lemma8 : ltr:ae op 
           -> atr:ae op 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i atr).l)))
                   (ensures (forall i e. mem e (union (project i ltr) (project i atr)).l <==>
                                    mem e (project i (union ltr atr)).l) /\
                            (forall i. (forall e e1. (mem e (union (project i ltr) (project i atr)).l /\ 
             mem e1 (union (project i ltr) (project i atr)).l /\ get_id e <> get_id e1 /\ 
                    (union (project i ltr) (project i atr)).vis e e1) <==>
            (mem e (project i (union ltr atr)).l /\ mem e1 (project i (union ltr atr)).l /\ get_id e <> get_id e1 /\
                   (project i (union ltr atr)).vis e e1))))

#set-options "--z3rlimit 10000000"
let lemma8 ltr atr = ()

val lemma9 : ltr:ae op 
           -> atr:ae op 
           -> btr:ae op 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l))/\
                             (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i atr).l)) /\
                             (forall i e. mem e (project i atr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                             (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i btr).l)))
                   (ensures (forall i. (forall e. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l <==>
                             mem e (project i (absmerge ltr atr btr)).l)) /\
             (forall i. (forall e e1. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l /\
                  mem e1 (absmerge (project i ltr) (project i atr) (project i btr)).l /\ get_id e <> get_id e1 /\
                              (absmerge (project i ltr) (project i atr) (project i btr)).vis e e1 <==>
                                mem e (project i (absmerge ltr atr btr)).l /\ mem e1 (project i (absmerge ltr atr btr)).l /\ get_id e <> get_id e1 /\ (project i (absmerge ltr atr btr)).vis e e1)))

#set-options "--z3rlimit 10000000"
let lemma9 ltr atr btr = ()

val prop_merge1 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> chs:list nat
                -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                  (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b) /\
                                  (forall i. mem i chs ==> mem_key_s i (merge ltr l atr a btr b)))
                        (ensures (forall i. mem i chs ==> 
                            (C.sim (project i (absmerge ltr atr btr)) (get_val_s i (merge ltr l atr a btr b)))))
                        (decreases chs)

#set-options "--z3rlimit 10000000"
let rec prop_merge1 ltr l atr a btr b lst =
  match lst with
  |[] -> ()
  |i::is -> lemma8 ltr atr; lemma8 ltr btr;
          lemma7 (project i (union ltr atr)) (get_val_s i a) (union (project i ltr) (project i atr));
          lemma7 (project i (union ltr btr)) (get_val_s i b) (union (project i ltr) (project i btr));
     C.prop_merge (project i ltr) (get_val_s i l) (project i atr) (get_val_s i a) (project i btr) (get_val_s i b);
          lemma9 ltr atr btr;
          lemma7 (absmerge (project i ltr) (project i atr) (project i btr)) 
                 (get_val_s i (merge ltr l atr a btr b)) (project i (absmerge ltr atr btr));
          assert (C.sim (project i (absmerge ltr atr btr)) (get_val_s i (merge ltr l atr a btr b)));
          prop_merge1 ltr l atr a btr b is

val prop_merge21 : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (forall e. mem e (merge ltr l atr a btr b) ==> 
                                      mem_key (get_key_s e) (absmerge ltr atr btr).l))

#set-options "--z3rlimit 10000000"
let prop_merge21 ltr l atr a btr b = 
  lemma2 (merge ltr l atr a btr b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge22 : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (forall e. mem e (absmerge ltr atr btr).l ==> 
                                      mem_key_s (get_key e) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge22 ltr l atr a btr b = 
  lemma2 (merge ltr l atr a btr b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge2 : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (forall ch. mem_key_s ch (merge ltr l atr a btr b) <==> 
                                       mem_key ch (absmerge ltr atr btr).l))

#set-options "--z3rlimit 10000000"
let prop_merge2 ltr l atr a btr b = 
  prop_merge21 ltr l atr a btr b;
  prop_merge22 ltr l atr a btr b

val prop_merge31 : ltr:ae op
                  -> l:s
                  -> atr:ae op
                  -> a:s
                  -> btr:ae op
                  -> b:s
                  -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                    (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                    (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                    (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                       (forall ch. mem_key_s ch (merge ltr l atr a btr b) <==> mem_key ch (absmerge ltr atr btr).l))
                          (ensures (forall e. mem e (absmerge ltr atr btr).l ==> 
                             (exists e1. mem e1 (merge ltr l atr a btr b) /\ get_key e = get_key_s e1)))

#set-options "--z3rlimit 10000000"
let prop_merge31 ltr l atr a btr b = 
  lemma2 (merge ltr l atr a btr b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge3 : ltr:ae op
                  -> l:s
                  -> atr:ae op
                  -> a:s
                  -> btr:ae op
                  -> b:s
                  -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                    (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                    (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                    (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                       (forall ch. mem_key_s ch (merge ltr l atr a btr b) <==> mem_key ch (absmerge ltr atr btr).l) /\
                       (forall e. mem e (absmerge ltr atr btr).l ==> 
                                 (exists e1. mem e1 (merge ltr l atr a btr b) /\ get_key e = get_key_s e1)))
                          (ensures (forall e. mem e (absmerge ltr atr btr).l ==> (exists e1. mem e1 (merge ltr l atr a btr b) /\
                                  get_key e = get_key_s e1 /\ mem (get_val e) (get_val_s1 e1))))

#set-options "--z3rlimit 10000000"
let prop_merge3 ltr l atr a btr b = 
  lemma2 (merge ltr l atr a btr b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr
  
val prop_merge : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  prop_merge2 ltr l atr a btr b;
  prop_merge31 ltr l atr a btr b;
  prop_merge3 ltr l atr a btr b;
  let m = get_lst (merge ltr l atr a btr b) in
  prop_merge1 ltr l atr a btr b m

instance _ : mrdt s op = {
  Library.sim = sim;
  Library.pre_cond_op = pre_cond_op;
  Library.app_op = app_op;
  Library.prop_oper = prop_oper;
  Library.pre_cond_merge = pre_cond_merge;
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence
}

