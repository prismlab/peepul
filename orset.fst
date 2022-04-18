module Orset
open FStar.List.Tot

open Library

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

type s = l:list (nat (*unique id*) * nat (*element*)) {unique_s l}

val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat) 
               -> Lemma (requires (unique_s l))
                       (ensures (unique_s (filter f l)))
                               [SMTPat (filter f l)]

#set-options "--z3rlimit 1000000"
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

type op =
  |Add : nat (*element*) -> op
  |Rem : nat (*element*) -> op

val get_ele : op1:(nat * op) -> Tot (ele:nat {(exists id. op1 = (id, Add ele) \/ op1 = (id, Rem ele))})
let get_ele op =
  match op with
  |(_, (Add ele)) -> ele
  |(_, (Rem ele)) -> ele

val opa : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id ele. op1 = (id, Add ele))})
let opa op1 =
  match op1 with
  |(_, Add _) -> true
  |_ -> false

val opr : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id ele. op1 = (id, Rem ele))})
let opr op1 = not (opa op1)

val pre_cond_op : s1:s
             -> op:(nat * op)
             -> Tot (b:bool {b=true <==> not (member_s (get_id op) s1)})
let pre_cond_op s1 op = not (member_s (get_id op) s1)

val app_op : s1:s
           -> op:(nat * op)
           -> Pure s
                 (requires pre_cond_op s1 op)
                 (ensures (fun res -> (opa op ==> (forall e. mem e s1 \/ e = ((get_id op), (get_ele op)) <==> mem e res)) /\
                                 (opr op ==> (forall e. mem e res <==> mem e s1 /\ snd e <> get_ele op))))
let app_op s1 op1 =
  match op1 with
  |(id, Add ele) -> (id, ele)::s1
  |(id, Rem ele) -> filter (fun e -> snd e <> ele) s1

val filter_uni1 : f:((nat * op) -> bool)
                -> l:list (nat * op) 
                -> Lemma (requires (unique_id l))
                        (ensures (unique_id (filter f l)))
                        [SMTPat (filter f l)]
let rec filter_uni1 f l = 
  match l with
  |[] -> ()
  |x::xs -> filter_uni1 f xs

val except : #a:eqtype 
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ not (f e)})
let rec except #a f l =
  match l with
  |[] -> []
  |hd::tl -> if not (f hd) then hd::(except f tl) else except f tl

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s 
        -> Tot (b:bool {b = true <==> (forall a. mem a s1 <==> (mem ((fst a), Add (snd a)) tr.l /\
                                   (forall r. mem r tr.l /\ fst a <> get_id r /\ opr r ==>
                                         not (snd a = get_ele r && (tr.vis ((fst a), Add (snd a)) r)))))})
let sim tr s1 =
  let lsta = (filter (fun a -> opa a) tr.l) in
  let lstr = (filter (fun r -> opr r) tr.l) in
  let lst = except (fun a -> (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

  forallb (fun e -> mem ((get_id e), (get_ele e)) s1) lst &&
  forallb (fun e -> mem ((fst e), Add (snd e)) lst) s1

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 1000000"
let prop_oper tr st op = ()

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. mem e a <==> mem e b))
let convergence tr a b = ()

val diff2 : a:list (nat * nat)
          -> l:list (nat * nat)
          -> Pure (list (nat * nat))
            (requires (unique_s a /\ unique_s l))
            (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\ unique_s d )) (decreases %[l;a;l;a])
let diff2 a l = 
  filter (fun e -> not (mem e l)) a

val remove : l:s 
           -> ele:(nat * nat)
           -> Pure s 
             (requires true)
             (ensures (fun res -> (forall e. mem e res <==> mem e l /\ e <> ele)))
let remove l ele =
  filter (fun e -> e <> ele) l

val merge1 : l:s
           -> a:s 
           -> b:s 
           -> Pure s 
             (requires (forall e. mem e (diff2 a l) ==> not (member_s (fst e) b)) /\
                       (forall e. mem e (diff2 b l) ==> not (member_s (fst e) a)))
             (ensures (fun res -> (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                               (mem e (diff2 a l)) \/ (mem e (diff2 b l)))))    (decreases %[l;a;b])
#set-options "--z3rlimit 10000"
let rec merge1 l a b = 
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> if (mem x a && mem x b) then x::(merge1 xs (remove a x) (remove b x)) 
                 else if (mem x a) then (merge1 xs (remove a x) b)
                   else if (mem x b) then (merge1 xs a (remove b x))
                     else (merge1 xs a b)
  |[],x::xs,_ -> x::(merge1 [] xs b)
  |[],[],x::xs -> b

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
                   (ensures (fun res -> (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                                     (mem e (diff2 a l)) \/ (mem e (diff2 b l)))))

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b = 
  merge1 l a b

val prop_merge : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
    assert (forall e. (mem e l /\ mem e a /\ mem e b) <==> (mem ((fst e), Add (snd e)) ltr.l /\ 
           (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\ opr r ==> 
           not (snd e = get_ele r && (absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))));

    assert (forall e. (mem e (diff2 a l)) <==> (mem ((fst e), Add (snd e)) atr.l /\ (forall r. mem r atr.l /\ fst e <> get_id r /\
           opr r ==> not (snd e = get_ele r && atr.vis ((fst e), Add (snd e)) r))));

    assert (forall e. (mem e (diff2 b l)) <==> (mem ((fst e), Add (snd e)) btr.l /\ (forall r. mem r btr.l /\ fst e <> get_id r /\
           opr r ==> not (snd e = get_ele r && btr.vis ((fst e), Add (snd e)) r))));

    assert (forall e. (mem ((fst e), Add (snd e)) ltr.l /\ (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\
           opr r ==> not (snd e = get_ele r && (absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))) \/ 
           (mem ((fst e), Add (snd e)) atr.l /\ (forall r. mem r atr.l /\ fst e <> get_id r /\ 
           opr r ==> not (snd e = get_ele r && atr.vis ((fst e), Add (snd e)) r))) \/
           (mem ((fst e), Add (snd e)) btr.l /\ (forall r. mem r btr.l /\ fst e <> get_id r /\ 
           opr r ==> not (snd e = get_ele r && btr.vis ((fst e), Add (snd e)) r))) <==>
           (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ 
           fst e <> get_id r /\ opr r ==> not (snd e = get_ele r && 
           (absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))));

    assert (forall e. ((mem e l /\ mem e a /\ mem e b) \/ (mem e (diff2 a l)) \/ (mem e (diff2 b l))) <==> 
           (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ 
           fst e <> get_id r /\ opr r ==> not (snd e = get_ele r && 
           (absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))));

    assert (forall e. (mem e (merge ltr l atr a btr b)) <==> 
           (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ 
           fst e <> get_id r /\ opr r ==> not (snd e = get_ele r && 
           (absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))));
    ()

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
