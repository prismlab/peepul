module Ctr
open FStar.List.Tot

open Library
type s = nat

type op = |Add 

val app_op : s1:s -> op:(nat * op) -> Tot (s2:s {(exists id. op = (id, Add) ==> s2 = s1 + 1)})
let app_op s op1 =
  match op1 with
  |(_,Add) -> s + 1

instance ctr : datatype s op = {
  Library.app_op = app_op
}

val sum : l:(list (nat * op))
        -> Tot (n:nat {n = (List.Tot.length  l)}) (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_, Add)::xs -> sum xs + 1

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> (s1 = sum tr.l)})
let sim tr s1 = (s1 = sum tr.l)

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (forall e. mem e tr.l ==> get_op e = get_op op) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))
let prop_oper tr st op = ()

val lemma1 : l:ae op
           -> a:ae op
           -> Lemma
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)))
               (ensures (forall e. mem e (union1 l a) <==> mem e l.l \/ mem e a.l) /\
                        (sum (union l a).l = sum l.l + sum a.l))
                        (decreases %[l.l;a.l])
                        [SMTPat (sum (union l a).l)]
#set-options "--z3rlimit 1000000"
let rec lemma1  l a =
    match l,a with
    |(A _ []), (A _ []) -> ()
    |(A _ (x::xs)), _ -> lemma1 (A l.vis xs) a
    |(A _ []), (A _ (x::xs)) -> lemma1 l (A a.vis xs)

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (fun res -> res = a + b - l))
#set-options "--z3rlimit 10000"
let merge ltr l atr a btr b = 
    lemma1 ltr atr;
    lemma1 ltr btr;
    a + b - l

val lemma2 : l:ae op
           -> a:ae op
           -> b:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                             (forall e. mem e l.l ==> not (member (get_id e) b.l)))
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
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))
#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma1 ltr atr; 
  lemma1 ltr btr;
  lemma2 ltr atr btr;
  ()

val convergence : tr:ae op
                 -> a:s
                 -> b:s
                 -> Lemma (requires (sim tr a /\ sim tr b))
                         (ensures a = b)
                         [SMTPat (sim tr a /\ sim tr b)]
let convergence tr a b = ()

instance _ : mrdt s op ctr = {
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence;
  Library.sim = sim;
  Library.prop_oper = prop_oper
}

