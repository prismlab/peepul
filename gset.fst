module Gset
open FStar.List.Tot

open Library

val unique_s : l:list nat
             -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |id::xs -> not (mem id xs) && unique_s xs

type s = l:list nat {unique_s l}

type rval = |Val : s -> rval
            |Bot

let init = []

type op =
  |Add : nat -> op
  |Rd

val forallo : f:((nat * op) -> bool)
            -> l:list (nat * op)
            -> Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forallo f l =
  match l with
  |[] -> true
  |hd::tl -> if f hd then forallo f tl else false

val opa : (nat * op) -> bool
let opa o = 
  match o with
  |(_, Add _) -> true
  |_ -> false

val get_ele : op1:(nat * op){opa op1} -> Tot (s:nat {op1 = (get_id op1, (Add s))}) 
let get_ele (id, (Add m)) = m

val mem_ele : ele:nat -> l:list (nat * op) -> Tot (b:bool {b = true <==> (exists id. mem (id, (Add ele)) l)})
let rec mem_ele ele l =
  match l with
  |[] -> false
  |(_, (Add ele1))::xs -> ele = ele1 || mem_ele ele xs
  |(_, Rd)::xs -> mem_ele ele xs

let pre_cond_op s1 op = true

val app_op : s1:s
           -> op:(nat * op)
           -> Pure (s * rval)
             (requires true)
             (ensures (fun res -> (opa op ==> (forall e. mem e (fst res) <==> mem e s1 \/ e = get_ele op)) /\
                               (not (opa op) ==> (forall e. mem e (fst res) <==> mem e s1))))
let app_op s1 op =
  match op with
  |(id, (Add ele)) -> if (mem ele s1) then (s1, Bot) else (ele::s1, Bot)
  |(id, Rd) -> (s1, Val s1)

val get_gset : tr:list (nat * op){unique_id tr} -> Tot (s1:s {(forall e. mem e s1 <==> mem_ele e tr)})
let rec get_gset l =
  match l with
  |[] -> []
  |(_, Add x)::xs -> if mem_ele x xs then get_gset xs else x::(get_gset xs)
  |(_, Rd)::xs -> get_gset xs

val spec : o:(nat * op) -> tr:ae op -> Tot rval
let spec o tr =
  match o with
  |(_, Add _) -> Bot
  |(_, Rd) -> Val (get_gset tr.l)

val extract : r:rval {exists v. r = Val v} -> s
let extract (Val s) = s

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> (forall e. mem e s1 <==> mem_ele e tr.l)})
#set-options "--z3rlimit 1000000"
let sim tr s1 =
 forallb (fun e -> mem_ele e tr.l) s1 &&
 forallo (fun e -> opa e && mem (get_ele e) s1) (filter (fun e1 -> opa e1) tr.l)

val remove_st : ele:nat
              -> s1:s {mem ele s1}
              -> Tot (s2:s {forall e. mem e s2 <==> mem e s1 /\ e <> ele})
let rec remove_st ele s1 =
  match s1 with
  |x::xs -> if x = ele then xs else x::remove_st ele xs

val lemma7 : tr:ae op -> s1:s -> tr1:ae op
           -> Lemma (requires sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                           (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                    mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                   (ensures (sim tr1 s1))
                   (decreases %[tr.l;s1;tr1.l])

#set-options "--z3rlimit 10000000"
let rec lemma7 tr s1 tr1 = 
  (*)match tr.l, tr1.l with
  |[], [] -> ()
  |(id, (Add v))::xs, _ -> 
        if (mem_ele v xs) then lemma7 (remove_op tr (id, (Add v))) s1 (remove_op tr (id, (Add v)))
          else lemma7 (remove_op tr (id, (Add v))) (remove_st v s1) (remove_op tr (id, (Add v)))
             |[], (_, (Add v))::xs -> ()*) ()

val pre_cond_merge1 : l:s -> a:s -> b:s
                    -> Tot (b1:bool {b1=true <==> (forall e. mem e l ==> mem e a /\ mem e b)})
let pre_cond_merge1 l a b = 
  forallb (fun e -> mem e a && mem e b) l

val merge1 : l:s
           -> a:s
           -> b:s
           -> Pure s
             (requires pre_cond_merge1 l a b)
             (ensures (fun u -> (forall e. mem e u <==> mem e a \/ mem e b)))
             (decreases %[l;a;b])

#set-options "--z3rlimit 10000000"
let rec merge1 l a b =
  match l, a, b with
  |[],[],[] -> []
  |x::xs, _, _ -> (merge1 xs a b) 
  |[],x::xs,_ -> if mem x b then (merge1 [] xs b) else x::(merge1 [] xs b)
  |[],[], _ -> b

val pre_cond_merge : ltr:ae op -> l:s -> atr:ae op -> a:s -> btr:ae op -> b:s -> Tot bool
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
                   (ensures (fun r -> r = merge1 l a b))

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
let prop_merge ltr l atr a btr b = ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (sim (append tr op) (get_st (app_op st op))))

#set-options "--z3rlimit 1000000"
let prop_oper tr st op = ()

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. mem e a <==> mem e b))
let convergence tr a b = ()

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (not (opa op) ==> (forall e. mem e (extract (get_rval (app_op st op))) <==>
                                                mem e (extract (spec op tr)))) /\
                               (opa op ==> get_rval (app_op st op) = spec op tr))
#set-options "--z3rlimit 1000000"
let prop_spec tr st op = ()

instance gset : mrdt s op rval = {
  Library.init = init;
  Library.spec = spec;
  Library.sim = sim;
  Library.pre_cond_op = pre_cond_op;
  Library.app_op = app_op;
  Library.prop_oper = prop_oper;
  Library.pre_cond_merge = pre_cond_merge;
  Library.pre_cond_merge1 = pre_cond_merge1;
  Library.merge1 = merge1;
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.prop_spec = prop_spec;
  Library.convergence = convergence
}
