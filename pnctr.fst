module Pnctr
open FStar.List.Tot

open Library

type s = int

type rval = |Val : s -> rval
            |Bot

type op =
  |Add
  |Rem
  |Rd

let init = 0

val opa : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id. op1 = (id,Add))})
let opa op1 =
  match op1 with
  |(id,Add) -> true
  |_ -> false

val opr : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id. op1 = (id,Rem))})
let opr op1 =
  match op1 with
  |(id,Rem) -> true
  |_ -> false

let pre_cond_app_op s1 op = true
let pre_cond_prop_oper tr s1 op = true

val app_op : s1:s -> op:(nat * op) 
           -> Tot (s2:(s * rval) {(opa op ==> s2 = (s1 + 1, Bot)) /\ 
                                 (opr op ==> s2 = (s1 - 1, Bot)) /\
                                 (not (opa op || opr op) ==> s2 = (s1, Val s1))})
let app_op s op1 =
  match op1 with
  |(_,Add) -> (s + 1, Bot)
  |(_,Rem) -> (s - 1, Bot)
  |(_,Rd) -> (s, Val s)

val sum : l:(list (nat * op))
        -> Tot (n:int {n = (List.Tot.length (filter (fun a -> opa a) l) - 
                         List.Tot.length (filter (fun a -> opr a) l))}) (decreases %[l])

let rec sum l =
  match l with
  |[] -> 0
  |(_, Add)::xs -> sum xs + 1
  |(_, Rem)::xs -> sum xs - 1
  |(_, Rd)::xs -> sum xs

val spec : o:(nat * op) -> tr:ae op -> Tot rval
let spec o tr =
  match o with
  |(_, Add) -> Bot
  |(_, Rem) -> Bot
  |(_, Rd) -> Val (sum tr.l)

val extract : r:rval {exists v. r = Val v} -> s
let extract (Val s) = s

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> (s1 = sum tr.l)})
let sim tr s1 = (s1 = sum tr.l)

val lemma1 : l:ae op
           -> a:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                   (ensures (forall e. mem e (union1 l a) <==> mem e l.l \/ mem e a.l) /\
                            (sum (union l a).l = sum l.l + sum a.l))
                            (decreases %[l.l;a.l])
                            [SMTPat (sum (union l a).l)]
#set-options "--z3rlimit 1000000"
let rec lemma1 l a =
  match l,a with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma1 (A l.vis xs) a
  |(A _ []), (A _ (x::xs)) -> lemma1 l (A a.vis xs)

let pre_cond_merge l a b = true
let pre_cond_prop_merge ltr l atr a btr b = true

val merge : l:s -> a:s -> b:s
           -> Pure s
             (requires true)
             (ensures (fun r -> r = a + b - l))
let merge l a b = a + b - l

val lemma2 : l:ae op
           -> a:ae op
           -> b:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                             (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))
                   (ensures (forall e. mem e (absmerge1 l a b) <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                            (sum (absmerge l a b).l = sum a.l + sum b.l + sum l.l))
                            (decreases %[l.l;a.l;b.l])
                            [SMTPat (sum (absmerge l a b).l)]
let rec lemma2 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma2 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma2 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma2 l a (A b.vis xs)

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
                       (ensures (sim (absmerge ltr atr btr) (merge l a b)))
#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma1 ltr atr; 
  lemma1 ltr btr;
  lemma2 ltr atr btr;
  ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (sim (append tr op) (get_st (app_op st op))))
let prop_oper tr st op = ()

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
                      (ensures (get_rval (app_op st op) = spec op tr))
#set-options "--z3rlimit 1000000"
let prop_spec tr st op = ()

instance pnctr : mrdt s op rval = {
  Library.init = init;
  Library.spec = spec;
  Library.sim = sim;
  Library.pre_cond_app_op = pre_cond_app_op;
  Library.pre_cond_prop_oper = pre_cond_prop_oper;
  Library.pre_cond_merge = pre_cond_merge;
  Library.pre_cond_prop_merge = pre_cond_prop_merge;
  Library.app_op = app_op;
  Library.merge = merge;
  Library.prop_oper = prop_oper;
  Library.prop_merge = prop_merge;
  Library.prop_spec = prop_spec;
  Library.convergence = convergence
}
