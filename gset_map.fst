module Gset_map
open FStar.List.Tot

open Library
open FStar.Tactics.Typeclasses

module A = Alpha_map

module G = Gset

val pre_cond_merge_a : l:A.s G.s -> a:A.s G.s -> b:A.s G.s 
                      -> Pure bool
                        (requires true)
                        (ensures (fun b1 -> (b1 = true <==> (forall e. A.mem_key_s e l ==> A.mem_key_s e a /\ A.mem_key_s e b) /\
                        (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                                           G.pre_cond_merge (A.get_val_s #G.s #G.op #G.rval ch l) 
                                           (A.get_val_s #G.s #G.op #G.rval ch a) (A.get_val_s #G.s #G.op #G.rval ch b)))))

let pre_cond_merge_a l a b = A.pre_cond_merge_a #G.s #G.op #G.rval l a b 

val merge_a : l:A.s G.s
             -> a:A.s G.s
             -> b:A.s G.s
             -> Pure (A.s G.s)
               (requires pre_cond_merge_a l a b)
               (ensures (fun r -> (forall ch. A.mem_key_s ch r <==> A.mem_key_s ch a \/ A.mem_key_s ch b) /\ A.unique_key r /\
                             (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> (A.get_val_s #G.s #G.op #G.rval ch r) =
                             (G.merge (A.get_val_s #G.s #G.op #G.rval ch l) (A.get_val_s #G.s #G.op #G.rval ch a) (A.get_val_s #G.s #G.op #G.rval ch b)))))
let merge_a l a b = A.merge_a #G.s #G.op #G.rval l a b

val lemma2 : s1:A.s G.s
           -> Lemma (requires true)
                   (ensures (forall e. mem e s1 ==> (A.get_val_s #G.s #G.op #G.rval (A.get_key_s e) s1 = A.get_val_s1 #G.s e)))
let rec lemma2  s1 =
  match s1 with
  |[] -> ()
  |x::xs -> lemma2 xs

val lemma4 : tr:ae (A.op G.op) -> s1:A.s G.s
           -> Lemma (requires A.sim_a #G.s #G.op #G.rval tr s1)
                   (ensures (forall i. (G.sim (A.project i tr) (A.get_val_s #G.s #G.op #G.rval i s1))))
let lemma4 tr s1 = ()

val lemma1 : tr:ae (A.op G.op)
         -> st:A.s G.s
         -> op1:(nat * (A.op G.op))
         -> Lemma (requires (A.sim_a #G.s #G.op #G.rval tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                           (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                          G.pre_cond_app_op (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) st) (A.project_op op1))
                 (ensures (forall i. A.mem_key_s i (get_st (A.app_op_a #G.s #G.op #G.rval st op1)) /\ i <> A.get_key op1 ==>
                 ((forall e. mem e (A.project i (append tr op1)).l <==> mem e (A.project i tr).l) /\
             (forall e e1. mem e (A.project i (append tr op1)).l /\ mem e1 (A.project i (append tr op1)).l /\ get_id e <> get_id e1 /\
                      (A.project i (append tr op1)).vis e e1 <==> 
                 mem e (A.project i tr).l /\ mem e1 (A.project i tr).l /\ get_id e <> get_id e1 /\ (A.project i tr).vis e e1) /\
             (A.get_val_s #G.s #G.op #G.rval i (get_st (A.app_op_a #G.s #G.op #G.rval st op1)) = (A.get_val_s #G.s #G.op #G.rval i st))) ==>
                          (G.sim (A.project i (append tr op1)) (A.get_val_s #G.s #G.op #G.rval i (get_st (A.app_op_a #G.s #G.op #G.rval st op1))))))

#set-options "--z3rlimit 10000000"
let lemma1 tr st op = ()

val lemma7 : tr:ae G.op -> s1:G.s -> tr1:ae G.op
           -> Lemma (requires G.sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                             (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                      mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                   (ensures (G.sim tr1 s1))
#set-options "--z3rlimit 10000000"
let lemma7 tr s1 tr1 = ()

val pre_cond_prop_merge_a : ltr:ae (A.op G.op) 
                     -> l:A.s G.s 
                     -> atr:ae (A.op G.op)
                     -> a:A.s G.s 
                     -> btr:ae (A.op G.op)
                     -> b:A.s G.s
                     -> Tot (b1:bool {b1=true <==> (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==>
                          (G.pre_cond_prop_merge (A.project ch ltr) (A.get_val_s #G.s #G.op #G.rval ch l)
                                            (A.project ch atr) (A.get_val_s #G.s #G.op #G.rval ch a)
                                            (A.project ch btr) (A.get_val_s #G.s #G.op #G.rval ch b)) /\
                              (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch atr).l)) /\
                              (forall e. mem e (A.project ch atr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                              (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                                (G.sim (A.project ch ltr) (A.get_val_s #G.s #G.op #G.rval ch l) /\ 
                      G.sim (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #G.s #G.op #G.rval ch a) /\
                     G.sim (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #G.s #G.op #G.rval ch b)))})

let pre_cond_prop_merge_a ltr l atr a btr b =
  forallb (fun ch -> (G.pre_cond_prop_merge (A.project ch ltr) (A.get_val_s #G.s #G.op #G.rval ch l)
                                    (A.project ch atr) (A.get_val_s #G.s #G.op #G.rval ch a)
                                    (A.project ch btr) (A.get_val_s #G.s #G.op #G.rval ch b)) &&
  (forallb (fun e -> not (mem_id (get_id e) (A.project ch atr).l)) (A.project ch ltr).l) &&
  (forallb (fun e -> not (mem_id (get_id e) (A.project ch btr).l)) (A.project ch atr).l) &&
  (forallb (fun e -> not (mem_id (get_id e) (A.project ch btr).l)) (A.project ch ltr).l) &&
  (G.sim (A.project ch ltr) (A.get_val_s #G.s #G.op #G.rval ch l)) &&
  (G.sim (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #G.s #G.op #G.rval ch a)) &&
  (G.sim (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #G.s #G.op #G.rval ch b))) (A.get_key_lst l a b)

instance _ : A.alpha_map G.s G.op G.rval G.gset = {
  A.lemma1 = lemma1;
  A.lemma4 = lemma4;
  A.lemma2 = lemma2;
  A.lemma7 = lemma7
}

val pre_cond_app_op_a : s1:(A.s G.s) -> op1:(nat * (A.op G.op))
                      -> Tot (b:bool {b = true <==> 
                           G.pre_cond_app_op (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) s1) (A.project_op op1)})
let pre_cond_app_op_a s1 op = 
  G.pre_cond_app_op (A.get_val_s #G.s #G.op #G.rval (A.get_key op) s1) (A.project_op op)

val pre_cond_prop_oper_a : tr:ae (A.op G.op)
                         -> st:(A.s G.s)
                         -> op1:(nat * (A.op G.op)) 
                         -> Pure bool
                           (requires (not (mem_id (get_id op1) tr.l) /\
                                     (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0))
                           (ensures (fun b -> (b=true <==> (G.pre_cond_prop_oper (A.project (A.get_key op1) (append tr op1))
                                    (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) st) (A.project_op op1)) /\
                                    G.pre_cond_app_op (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) st) (A.project_op op1) /\
                           (G.sim (A.project (A.get_key op1) (append tr op1)) (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) (get_st (A.app_op_a #G.s #G.op #G.rval st op1)))))))

let pre_cond_prop_oper_a tr st op1 =
    G.pre_cond_prop_oper (A.project (A.get_key op1) (append tr op1))
                         (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) st) (A.project_op op1) &&
    G.pre_cond_app_op (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) st) (A.project_op op1) &&
    G.sim (A.project (A.get_key op1) (append tr op1)) (A.get_val_s #G.s #G.op #G.rval (A.get_key op1) 
                     (get_st (A.app_op_a #G.s #G.op #G.rval st op1)))

val prop_oper_a : tr:ae (A.op G.op)
              -> st:A.s G.s
              -> op1:(nat * (A.op G.op)) 
              -> Lemma (requires (A.sim_a #G.s #G.op #G.rval tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                pre_cond_app_op_a st op1 /\ pre_cond_prop_oper_a tr st op1)
                      (ensures (A.sim_a #G.s #G.op #G.rval (append tr op1) (get_st (A.app_op_a #G.s #G.op #G.rval st op1))))

#set-options "--z3rlimit 10000000"
let prop_oper_a tr st op = 
    A.prop_oper_a #G.s #G.op #G.rval #G.gset tr st op

val convergence_a : tr:ae (A.op G.op)
                  -> a:A.s G.s
                  -> b:A.s G.s
                  -> Lemma (requires (A.sim_a #G.s #G.op #G.rval tr a /\ A.sim_a #G.s #G.op #G.rval tr b))
                          (ensures (forall e. A.mem_key_s e a <==> A.mem_key_s e b) /\
                                      (forall ch. A.mem_key_s ch a /\ A.mem_key_s ch b ==> 
            (forall e. mem e (A.get_val_s #G.s #G.op #G.rval ch a) <==> mem e (A.get_val_s #G.s #G.op #G.rval ch b))))

#set-options "--z3rlimit 100000000"
let convergence_a tr a b = 
  A.convergence_a1 #G.s #G.op #G.rval tr a b

val prop_merge_a : ltr:ae (A.op G.op)
          -> l:(A.s G.s)
            -> atr:ae (A.op G.op)
            -> a:(A.s G.s)
            -> btr:ae (A.op G.op)
            -> b:(A.s G.s)
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (A.sim_a #G.s #G.op #G.rval ltr l /\ A.sim_a #G.s #G.op #G.rval (union ltr atr) a /\ A.sim_a #G.s #G.op #G.rval (union ltr btr) b) /\
                             pre_cond_merge_a l a b /\
                             (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                         (pre_cond_prop_merge #G.s #G.op #G.rval (A.project ch ltr) (A.get_val_s #G.s #G.op #G.rval ch l)
                                             (A.project ch atr) (A.get_val_s #G.s #G.op #G.rval ch a)
                                             (A.project ch btr) (A.get_val_s #G.s #G.op #G.rval ch b)) /\
                            (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch atr).l)) /\
                            (forall e. mem e (A.project ch atr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                            (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                (sim #G.s #G.op #G.rval (A.project ch ltr) (A.get_val_s #G.s #G.op #G.rval ch l) /\ sim #G.s #G.op #G.rval (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #G.s #G.op #G.rval ch a) /\ sim #G.s #G.op #G.rval (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #G.s #G.op #G.rval ch b))))
                (ensures (A.sim_a #G.s #G.op #G.rval (absmerge ltr atr btr) (merge_a l a b)))

#set-options "--z3rlimit 10000000"
let prop_merge_a ltr l atr a btr b = 
  A.prop_merge_a #G.s #G.op #G.rval #G.gset ltr l atr a btr b

val extract : r:G.rval {r <> G.Bot} -> G.s
let extract (G.Val s) = s

val spec_a : o1:(nat * (A.op G.op))
           -> tr:ae (A.op G.op)
           -> Pure G.rval
             (requires true)
             (ensures (fun res -> A.opget o1 ==> (res = G.spec (A.project_op o1) (A.project (A.get_key o1) tr))))
let spec_a o1 tr = G.spec (A.project_op o1) (A.project (A.get_key o1) tr)

val prop_spec_a : tr:ae (A.op G.op)
                  -> st1:(A.s G.s)
                  -> op:(nat * (A.op G.op))
                  -> Lemma (requires (A.sim_a #G.s #G.op #G.rval tr st1) /\ (not (mem_id (get_id op) tr.l)) /\
                                    (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0 /\
                                    pre_cond_app_op_a st1 op)
                    (ensures (A.opget op ==>
                             ((G.opa (A.project_op op) ==> (get_rval (A.app_op_a #G.s #G.op #G.rval st1 op)) =
                                                  ((A.spec_a #G.s #G.op #G.rval) op tr)) /\
                (not (G.opa (A.project_op op)) ==> 
                     (forall e. mem e (extract (get_rval (A.app_op_a #G.s #G.op #G.rval st1 op))) <==> 
                           mem e (extract ((A.spec_a #G.s #G.op #G.rval) op tr)))))))

#set-options "--z3rlimit 1000000"
let prop_spec_a tr st op = ()

val sim_a : tr:ae (A.op G.op)
          -> s1:(A.s G.s)
          -> Tot (b:bool {(b = true) <==> (forall e1. mem e1 s1 ==> (exists e. mem e tr.l /\ A.get_key_s e1 = A.get_key e /\ A.opset e)) /\
                (forall k. A.mem_key_s k s1 ==> G.sim (A.project k tr) (A.get_val_s #G.s #G.op #G.rval k s1)) /\
                (forall e. mem e tr.l /\ A.opset e ==> (exists e1. mem e1 s1 /\ A.get_key e = A.get_key_s e1))})
let sim_a tr s1 = 
    A.sim_a #G.s #G.op #G.rval tr s1

#set-options "--z3rlimit 10000000" 
instance gset_map : mrdt (A.s G.s) (A.op G.op) (G.rval) = {
  Library.init = A.init_a;
  Library.spec = spec_a;
  Library.sim = sim_a;
  Library.pre_cond_app_op = pre_cond_app_op_a;
  Library.pre_cond_prop_oper = pre_cond_prop_oper_a;
  Library.pre_cond_merge = pre_cond_merge_a;
  Library.pre_cond_prop_merge = pre_cond_prop_merge_a;
  Library.app_op = A.app_op_a;
  Library.merge = merge_a;
  Library.prop_oper = prop_oper_a;
  Library.prop_merge = prop_merge_a;
  Library.prop_spec = prop_spec_a;
  Library.convergence = convergence_a
}
