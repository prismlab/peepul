module Ictr
open FStar.List.Tot

#set-options "--query_stats"

open Library

(** Concrete state of the MRDT*)
type s = nat


(** Operations supported by the MRDT*)
type op = |Add
          |Rd


(** Return value of the operations*)
type rval = |Val : s -> rval
            |Bot


(** Initial state*)
let init = 0


let pre_cond_do s1 op = true
let pre_cond_prop_do tr s1 op = true


(** Concrete DO function*)
val do : s1:s -> o:(nat * op) -> Tot (s2:(s * rval) {get_op o = Add ==> s2 = (s1 + 1, Bot) /\
                                                 get_op o = Rd ==> s2 = (s1, Val s1)})
let do s1 o =
  match o with
  |(_,Add) -> (s1 + 1, Bot)
  |(_,Rd) -> (s1, Val s1)

val sum : l:(list (nat * op))
        -> Tot (n:nat {n = (List.Tot.length (filter (fun e -> get_op e = Add) l))}) 
          (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_, Add)::xs -> sum xs + 1
  |(_, Rd)::xs -> sum xs


(** Specification of the MRDT*)
val spec : o:(nat * op) -> tr:ae op -> rval
let spec o tr =
  match o with
  |(_, Add) -> Bot
  |(_, Rd) -> Val (sum tr.l)


(** Simulation relation*)
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> (s1 = sum tr.l)})
let sim tr s1 = (s1 = sum tr.l)


(** Proof of no. of Add operations seen by branch A = no. of Add ops seen by LCA + 
                                                      no. of Add ops seen by branch A which are not seen by LCA
    This is needed to show that the concrete state of a >= concrete state of lca.
    The result of the 3-way merge (a + b - l) is a natural number. 
    Only with this additional lemma, the merge function will type check. *)
val sum_union : l_l:list(nat * op) {unique_id l_l}
              -> a_l:list(nat * op) {unique_id a_l}
              -> Lemma (requires (forall e. mem e l_l ==> not (mem_id (get_id e) a_l)))
                      (ensures (sum (union1 l_l a_l) = sum l_l + sum a_l))
let rec sum_union l_l a_l =
  match l_l, a_l with
  |[],[] -> ()
  |x::xs,_ -> sum_union xs a_l
  |[],_ -> ()

let pre_cond_merge l a b = a >= l && b >= l

let pre_cond_prop_merge ltr l atr a btr b = true


(** Concrete THREE_WAY MERGE function*)
val merge : l:s -> a:s -> b:s
          -> Pure s (requires pre_cond_merge l a b)
                   (ensures (fun r -> r = a + b - l))
let merge l a b = a + b - l


val sum_absmerge : l_l:list(nat * op) {unique_id l_l}
                 -> a_l:list(nat * op) {unique_id a_l}
                 -> b_l:list(nat * op) {unique_id b_l}
                 -> Lemma (requires (forall e. mem e l_l ==> not (mem_id (get_id e) a_l)) /\
                                   (forall e. mem e a_l ==> not (mem_id (get_id e) b_l)) /\
                                   (forall e. mem e l_l ==> not (mem_id (get_id e) b_l)))
                         (ensures (forall e. mem e (abs_merge1 l_l a_l b_l) <==> mem e l_l \/ mem e a_l \/ mem e b_l) /\
                                  (sum (abs_merge1 l_l a_l b_l) = sum a_l + sum b_l + sum l_l))
                         (decreases %[l_l;a_l;b_l])
#set-options "--z3rlimit 1000"
let rec sum_absmerge l_l a_l b_l =
  match l_l,a_l,b_l with
  |[],[],[] -> ()
  |x::xs,_,_ -> sum_absmerge xs a_l b_l
  |[],x::xs,_ -> sum_absmerge [] xs b_l
  |[],[],_ -> ()


(** Proof of operations*)
val prop_do : tr:ae op
            -> st:s
            -> op:(nat * op)
            -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                              (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                    (ensures (sim (abs_do tr op) (get_st (do st op))))
let prop_do tr st op = ()


(** Proof of three-way merge*)
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
  sum_union ltr.l atr.l; assert (a >= l);
  sum_union ltr.l btr.l; assert (b >= l);
  sum_absmerge ltr.l atr.l btr.l



(** Proof of implementation satisfying the specification*)
val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (get_rval (do st op) = spec op tr))
let prop_spec tr st op = ()


(** Proof of convergence*)
val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures a = b)
let convergence tr a b = ()


(** ictr is an instance of the MRDT type class satisfying the conditions*)
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

