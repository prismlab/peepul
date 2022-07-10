module Ictr
open FStar.List.Tot

#set-options "--query_stats"

open Library

type s = nat

type rval = |Val : s -> rval
            |Bot

type op = |Add
          |Rd

let init = 0

let pre_cond_do s1 op = true
let pre_cond_prop_do tr s1 op = true

val do : s1:s -> op:(nat * op) -> Tot (s2:(s * rval) {get_op op = Add ==> s2 = (s1 + 1, Bot) /\
                                                  get_op op = Rd ==> s2 = (s1, Val s1)})
let do s op1 =
  match op1 with
  |(_,Add) -> (s + 1, Bot)
  |(_,Rd) -> (s, Val s)

val sum : l:(list (nat * op))
        -> Tot (n:nat {n = (List.Tot.length (filter (fun e -> get_op e = Add) l))}) (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_, Add)::xs -> sum xs + 1
  |(_, Rd)::xs -> sum xs

val spec : o:(nat * op) -> tr:ae op -> rval
let spec o tr =
  match o with
  |(_, Add) -> Bot
  |(_, Rd) -> Val (sum tr.l)

val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> (s1 = sum tr.l)})
let sim tr s1 = (s1 = sum tr.l)

val lemma11 : l:list(nat * op) {unique_id l}
            -> a:list(nat * op) {unique_id a}
            -> Lemma (requires (forall e. mem e l ==> not (mem_id (get_id e) a)))
                    (ensures (sum (union1 l a) = sum l + sum a))
let rec lemma11 l a =
  match l,a with
  |[],[] -> ()
  |x::xs,_ -> lemma11 xs a
  |[],_ -> ()

val lemma1 : l:ae op
           -> a:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                   (ensures (forall e. mem e (union l a).l <==> mem e l.l \/ mem e a.l) /\
                            (sum (union l a).l = sum l.l + sum a.l))
let lemma1 l a = lemma11 l.l a.l

let pre_cond_merge l a b = a >= l && b >= l

let pre_cond_prop_merge ltr l atr a btr b = true

val merge : l:s -> a:s -> b:s
          -> Pure s
            (requires pre_cond_merge l a b)
            (ensures (fun r -> r = a + b - l))
let merge l a b = a + b - l

val lemma21 : l:list(nat * op) {unique_id l}
            -> a:list(nat * op) {unique_id a}
            -> b:list(nat * op) {unique_id b}
            -> Lemma (requires (forall e. mem e l ==> not (mem_id (get_id e) a)) /\
                              (forall e. mem e a ==> not (mem_id (get_id e) b)) /\
                              (forall e. mem e l ==> not (mem_id (get_id e) b)))
                    (ensures (forall e. mem e (abs_merge1 l a b) <==> mem e l \/ mem e a \/ mem e b) /\
                             (sum (abs_merge1 l a b) = sum a + sum b + sum l))
                             (decreases %[l;a;b])
#set-options "--z3rlimit 1000"
let rec lemma21 l a b =
  match l,a,b with
  |[],[],[] -> ()
  |x::xs,_,_ -> lemma21 xs a b
  |[],x::xs,_ -> lemma21 [] xs b
  |[],[],_ -> ()

val lemma2 : l:ae op
           -> a:ae op
           -> b:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                             (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))
                   (ensures (forall e. mem e (abs_merge l a b).l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                            (sum (abs_merge l a b).l = sum a.l + sum b.l + sum l.l))
let lemma2 l a b = lemma21 l.l a.l b.l

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
                       (ensures (pre_cond_merge l a b) /\ (sim (abs_merge ltr atr btr) (merge l a b)))
#set-options "--z3rlimit 1000"
let prop_merge ltr l atr a btr b = 
  lemma1 ltr atr; 
  lemma1 ltr btr;
  lemma2 ltr atr btr;
  ()

val prop_do : tr:ae op
            -> st:s
            -> op:(nat * op)
            -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                              (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                    (ensures (sim (abs_do tr op) (get_st (do st op))))
let prop_do tr st op = ()

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures a = b)
let convergence tr a b = ()

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (get_rval (do st op) = spec op tr))
let prop_spec tr st op = ()

instance ictr : mrdt s op rval = {
  Library.init = init;
  Library.spec = spec;
  Library.sim = sim;
  Library.pre_cond_do = pre_cond_do;
  Library.pre_cond_prop_do = pre_cond_prop_do;
  Library.pre_cond_merge = pre_cond_merge;
  Library.pre_cond_prop_merge = pre_cond_prop_merge;
  Library.do = do;
  Library.merge = merge;
  Library.prop_do = prop_do;
  Library.prop_merge = prop_merge;
  Library.prop_spec = prop_spec;
  Library.convergence = convergence
}

