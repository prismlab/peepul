module Ictr_new_refactored

open FStar.List.Tot
open Helper

type op =
  |Inc : nat -> op

type o = (nat (*unique id*) * op)

let get_ele (_,Inc n) = n

type s = nat

val app_op : s -> o -> s
let app_op c (_,Inc n) = c + n

type ae = Helper.ae op

val sum : l:(list o) -> Tot nat (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |((_,Inc n)::xs) -> n + sum xs

val sim_prop : s -> ae -> s -> bool -> prop
let sim_prop s0 tr s1 b = (s1 = s0 + sum tr.l) <==> b = true

val sim : Helper.sim_type op s sim_prop 
let sim s0 tr s1 = (s1 = s0 + sum tr.l)

val absmerge1 : l:ae
             -> a:ae 
             -> b:ae
             -> Pure (list o)
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                         (forall e. mem e b.l ==> not (member (get_id e) l.l)))
               (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique u)))
               (decreases %[l.l;a.l;b.l])
let rec absmerge1 l a b =
    match l,a,b with
    |(A _ []), (A _ []), (A _ []) -> []
    |(A _ (x::xs)), _, _ -> x::(absmerge1 (A l.vis xs) a b)
    |(A _ []), (A _ (x::xs)), _ -> x::(absmerge1 l (A a.vis xs) b)
    |(A _ []), (A _ []), (A _ (x::xs)) -> x::(absmerge1 l a (A b.vis xs))

val absmerge : Helper.abs_merge_type op
let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1) || 
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1)) (absmerge1 l a b))

val lemma1 : l:ae
           -> a:ae
           -> b:ae
           -> Lemma
             (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                       (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                       (forall e. mem e b.l ==> not (member (get_id e) l.l)))
             (ensures (forall e. mem e (absmerge1 l a b) <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                      (sum (absmerge l a b).l = sum a.l + sum b.l + sum l.l))
             (decreases %[l.l;a.l;b.l])
let rec lemma1 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma1 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma1 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma1 l a (A b.vis xs)

val merge : Helper.merge_type op s sim_prop sim
let merge s0 ltr l atr a btr b =
  a + b - l

val prop_merge : Helper.prop_merge_type op s sim_prop sim merge absmerge
let prop_merge s0 ltr l atr a btr b =
    lemma1 ltr atr btr; ()

val append1 : tr:ae
            -> op:o
            -> Pure (list o)
              (requires (not (member (get_id op) tr.l)))
              (ensures (fun res -> (forall e. mem e res <==> mem e tr.l \/ e = op)))
let append1 tr op = (op::tr.l)

val append : Helper.append_type op
let append tr op =
    (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                 (mem o tr.l && o1 = op && get_id o <> get_id op)) (append1 tr op))

val prop_oper : Helper.prop_oper_type op s app_op sim_prop sim append
let prop_oper s0 tr st op = ()

val convergence : s0:s
                -> tr:ae
                -> a:s
                -> b:s
                -> Lemma (requires (sim s0 tr a /\ sim s0 tr b))
                        (ensures (a = b))
let convergence s0 tr a b = ()
