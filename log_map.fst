module Log_map
open FStar.List.Tot

#set-options "--query_stats"

open Library

module A = Alpha_map

module L = Log

val pre_cond_merge_a : l:A.s L.s -> a:A.s L.s -> b:A.s L.s 
                      -> Pure bool
                        (requires true)
                        (ensures (fun b1 -> (b1 = true <==> (forall e. A.mem_key_s e l ==> A.mem_key_s e a /\ A.mem_key_s e b) /\
                          (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                            (L.pre_cond_merge (A.get_val_s #L.s #L.op #L.rval ch l) 
                            (A.get_val_s #L.s #L.op #L.rval ch a) (A.get_val_s #L.s #L.op #L.rval ch b))))))

#set-options "--z3rlimit 1000"
let pre_cond_merge_a l a b = 
  forallb (fun e -> A.mem_key_s (A.get_key_s #L.s e) a && A.mem_key_s (A.get_key_s #L.s e) b) l &&
  forallb (fun ch -> L.pre_cond_merge (A.get_val_s #L.s #L.op #L.rval ch l) (A.get_val_s #L.s #L.op #L.rval ch a)  (A.get_val_s #L.s #L.op #L.rval ch b)) (A.get_key_lst l a b)

val merge_a : l:A.s L.s
             -> a:A.s L.s
             -> b:A.s L.s
             -> Pure (A.s L.s)
               (requires pre_cond_merge_a l a b)
               (ensures (fun r -> (forall ch. A.mem_key_s ch r <==> A.mem_key_s ch a \/ A.mem_key_s ch b) /\ A.unique_key r /\
                               (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> (A.get_val_s #L.s #L.op #L.rval ch r) =
                               (L.merge (A.get_val_s #L.s #L.op #L.rval ch l) (A.get_val_s #L.s #L.op #L.rval ch a) (A.get_val_s #L.s #L.op #L.rval ch b)))))

let merge_a l a b = A.merge_a #L.s #L.op #L.rval l a b

val lemma2 : s1:A.s L.s
           -> Lemma (requires true)
                   (ensures (forall e. mem e s1 ==> (A.get_val_s #L.s #L.op #L.rval (A.get_key_s e) s1 = A.get_val_s1 #L.s e)))
let rec lemma2 s1 =
  match s1 with
  |[] -> ()
  |x::xs -> lemma2 xs

val lemma4 : tr:ae (A.op L.op) -> s1:A.s L.s
           -> Lemma (requires A.sim_a #L.s #L.op #L.rval tr s1)
                   (ensures (forall i. (L.sim (A.project i tr) (A.get_val_s #L.s #L.op #L.rval i s1))))
let lemma4 tr s1 = ()

val lemma1 : tr:ae (A.op L.op)
         -> st:A.s L.s
         -> op1:(nat * (A.op L.op))
         -> Lemma (requires (A.sim_a #L.s #L.op #L.rval tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                           (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                          L.pre_cond_do (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) st) (A.project_op op1))
                 (ensures (forall i. A.mem_key_s i (get_st (A.do_a #L.s #L.op #L.rval st op1)) /\ i <> A.get_key op1 ==>
                 ((forall e. mem e (A.project i (abs_do tr op1)).l <==> mem e (A.project i tr).l) /\
             (forall e e1. mem e (A.project i (abs_do tr op1)).l /\ mem e1 (A.project i (abs_do tr op1)).l /\ get_id e <> get_id e1 /\
                      (A.project i (abs_do tr op1)).vis e e1 <==> 
                 mem e (A.project i tr).l /\ mem e1 (A.project i tr).l /\ get_id e <> get_id e1 /\ (A.project i tr).vis e e1) /\
             (A.get_val_s #L.s #L.op #L.rval i (get_st (A.do_a #L.s #L.op #L.rval st op1)) = (A.get_val_s #L.s #L.op #L.rval i st))) ==>
                          (L.sim (A.project i (abs_do tr op1)) (A.get_val_s #L.s #L.op #L.rval i (get_st (A.do_a #L.s #L.op #L.rval st op1))))))

#set-options "--z3rlimit 1000"
let lemma1 tr st op = ()

val lemma7 : tr:ae L.op -> s1:L.s -> tr1:ae L.op
           -> Lemma (requires L.sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                             (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                      mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                   (ensures (L.sim tr1 s1))
#set-options "--z3rlimit 1000"
let lemma7 tr s1 tr1 = ()

instance _ : A.alpha_map L.s L.op L.rval L.log = {
  A.lemma1 = lemma1;
  A.lemma4 = lemma4;
  A.lemma2 = lemma2;
  A.lemma7 = lemma7
}

val pre_cond_prop_merge_a : ltr:ae (A.op L.op) 
                     -> l:A.s L.s 
                     -> atr:ae (A.op L.op)
                     -> a:A.s L.s 
                     -> btr:ae (A.op L.op)
                     -> b:A.s L.s
                     -> Tot (b1:bool {b1=true <==> (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==>
                          (L.pre_cond_prop_merge (A.project ch ltr) (A.get_val_s #L.s #L.op #L.rval ch l)
                                                 (A.project ch atr) (A.get_val_s #L.s #L.op #L.rval ch a)
                                                 (A.project ch btr) (A.get_val_s #L.s #L.op #L.rval ch b)) /\
                              (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch atr).l)) /\
                              (forall e. mem e (A.project ch atr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                              (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                     (L.sim (A.project ch ltr) (A.get_val_s #L.s #L.op #L.rval ch l) /\ 
                      L.sim (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #L.s #L.op #L.rval ch a) /\
                      L.sim (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #L.s #L.op #L.rval ch b)))})

let pre_cond_prop_merge_a ltr l atr a btr b =
  forallb (fun ch -> (L.pre_cond_prop_merge (A.project ch ltr) (A.get_val_s #L.s #L.op #L.rval ch l)
                                    (A.project ch atr) (A.get_val_s #L.s #L.op #L.rval ch a)
                                    (A.project ch btr) (A.get_val_s #L.s #L.op #L.rval ch b)) &&
  forallb (fun e -> not (mem_id (get_id e) (A.project ch atr).l)) (A.project ch ltr).l &&
  forallb (fun e -> not (mem_id (get_id e) (A.project ch btr).l)) (A.project ch atr).l &&
  forallb (fun e -> not (mem_id (get_id e) (A.project ch btr).l)) (A.project ch ltr).l &&
  L.sim (A.project ch ltr) (A.get_val_s #L.s #L.op #L.rval ch l) &&
  L.sim (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #L.s #L.op #L.rval ch a) &&
  L.sim (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #L.s #L.op #L.rval ch b)) (A.get_key_lst l a b)

val pre_cond_do_a : s1:(A.s L.s) -> op1:(nat * (A.op L.op))
                  -> Tot (b:bool {b = true <==> 
                        L.pre_cond_do (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) s1) (A.project_op op1)})
let pre_cond_do_a s1 op = 
  L.pre_cond_do (A.get_val_s #L.s #L.op #L.rval (A.get_key op) s1) (A.project_op op)

val pre_cond_prop_do_a : tr:ae (A.op L.op)
                       -> st:(A.s L.s)
                       -> op1:(nat * (A.op L.op)) 
                       -> Pure bool
                         (requires (not (mem_id (get_id op1) tr.l) /\
                                   (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0))
                         (ensures (fun b -> (b=true <==> (L.pre_cond_prop_do (A.project (A.get_key op1) tr)
                                  (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) st) (A.project_op op1)) /\
                              L.pre_cond_do (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) st) (A.project_op op1) /\
                           (L.sim (A.project (A.get_key op1) (abs_do tr op1)) (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) (get_st (A.do_a #L.s #L.op #L.rval st op1)))))))

let pre_cond_prop_do_a tr st op1 =
    L.pre_cond_prop_do (A.project (A.get_key op1) tr)
                         (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) st) (A.project_op op1) &&
    L.pre_cond_do (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) st) (A.project_op op1) &&
    L.sim (A.project (A.get_key op1) (abs_do tr op1)) (A.get_val_s #L.s #L.op #L.rval (A.get_key op1) 
                     (get_st (A.do_a #L.s #L.op #L.rval st op1)))

val prop_do_a : tr:ae (A.op L.op)
              -> st:A.s L.s
              -> op1:(nat * (A.op L.op)) 
              -> Lemma (requires (A.sim_a #L.s #L.op #L.rval tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                pre_cond_do_a st op1 /\ pre_cond_prop_do_a tr st op1)
                      (ensures (A.sim_a #L.s #L.op #L.rval (abs_do tr op1) (get_st (A.do_a #L.s #L.op #L.rval st op1))))

#set-options "--z3rlimit 1000"
let prop_do_a tr st op = 
  A.prop_do_a #L.s #L.op #L.rval #L.log tr st op

val convergence2 : tr:ae (A.op L.op)
                 -> a:(A.s L.s)
                 -> b:(A.s L.s)
                 -> Lemma (requires (A.sim_a #L.s #L.op #L.rval tr a /\ A.sim_a #L.s #L.op #L.rval tr b))
                         (ensures (forall ch. A.mem_key_s ch a /\ A.mem_key_s ch b ==> 
         (forall e e1. mem e (A.get_val_s #L.s #L.op #L.rval ch a) /\ mem e1 (A.get_val_s #L.s #L.op #L.rval ch a) /\ 
                    L.fst e <> L.fst e1 /\ L.fst e > L.fst e1 /\ L.ord e e1 (A.get_val_s #L.s #L.op #L.rval ch a)  <==> 
    mem e (A.get_val_s #L.s #L.op #L.rval ch b) /\ mem e1 (A.get_val_s #L.s #L.op #L.rval ch b) /\ L.fst e <> L.fst e1 /\
                    L.fst e > L.fst e1 /\ L.ord e e1 (A.get_val_s #L.s #L.op #L.rval ch b))) /\
          (forall ch. A.mem_key_s ch a /\ A.mem_key_s ch b ==>
    (forall e. L.mem_id_s e (A.get_val_s #L.s #L.op #L.rval ch a) <==> L.mem_id_s e (A.get_val_s #L.s #L.op #L.rval ch b))))

#set-options "--z3rlimit 1000"
let convergence2 tr a b = 
  A.convergence_a1 #L.s #L.op #L.rval tr a b

val lem_length : a:(A.s L.s)
               -> b:(A.s L.s)
               -> lst:list string
               -> Lemma (requires (forall ch. mem ch lst ==> A.mem_key_s ch a /\ A.mem_key_s ch b) /\
                                          (forall e. A.mem_key_s e a <==> A.mem_key_s e b) /\
                                    A.unique_keys lst /\ (forall ch. mem ch lst ==> 
                 (forall e. L.mem_id_s e (A.get_val_s #L.s #L.op #L.rval ch a) <==> L.mem_id_s e (A.get_val_s #L.s #L.op #L.rval ch b))))
                 (ensures (forall ch. mem ch lst ==> (List.Tot.length (A.get_val_s #L.s #L.op #L.rval ch a) = List.Tot.length (A.get_val_s #L.s #L.op #L.rval ch b))))
                          (decreases lst)

let rec lem_length a b lst =
  match lst with
  |[] -> ()
  |ch::chs -> L.lem_length (A.get_val_s #L.s #L.op #L.rval ch a) (A.get_val_s #L.s #L.op #L.rval ch b); 
            lem_length a b chs

val convergence3 : a:(A.s L.s)
                 -> b:(A.s L.s)
                 -> lst:list string
                 -> Lemma (requires (forall ch. mem ch lst ==> A.mem_key_s ch a /\ A.mem_key_s ch b) /\
                                   (forall e. A.mem_key_s e a <==> A.mem_key_s e b) /\
                                    A.unique_keys lst /\ (forall ch. mem ch lst ==> 
    (forall e. L.mem_id_s e (A.get_val_s #L.s #L.op #L.rval ch a) <==> L.mem_id_s e (A.get_val_s #L.s #L.op #L.rval ch b))) /\
    (forall ch. mem ch lst ==> (forall e. mem e (A.get_val_s #L.s #L.op #L.rval ch a) <==> mem e (A.get_val_s #L.s #L.op #L.rval ch b))) /\
                   (forall ch. mem ch lst ==> (List.Tot.length (A.get_val_s #L.s #L.op #L.rval ch a) = List.Tot.length (A.get_val_s #L.s #L.op #L.rval ch b))) /\
                    (forall ch. mem ch lst ==> 
           (forall e e1. mem e (A.get_val_s #L.s #L.op #L.rval ch a) /\ mem e1 (A.get_val_s #L.s #L.op #L.rval ch a) /\ 
                   L.fst e <> L.fst e1 /\ L.fst e > L.fst e1 /\ L.ord e e1 (A.get_val_s #L.s #L.op #L.rval ch a)  <==> 
                   mem e (A.get_val_s #L.s #L.op #L.rval ch b) /\ mem e1 (A.get_val_s #L.s #L.op #L.rval ch b) /\ 
                   L.fst e <> L.fst e1 /\ L.fst e > L.fst e1 /\ L.ord e e1 (A.get_val_s #L.s #L.op #L.rval ch b))))
                          (ensures (forall ch. mem ch lst ==> (A.get_val_s #L.s #L.op #L.rval ch a = 
                                                         A.get_val_s #L.s #L.op #L.rval ch b)))
                         (decreases lst)
#set-options "--z3rlimit 10000"
let rec convergence3 a b lst =
  match lst with
  |[] -> ()
  |ch::chs -> L.lem_same (A.get_val_s #L.s #L.op #L.rval ch a) (A.get_val_s #L.s #L.op #L.rval ch b);
            convergence3 a b chs

val convergence_a : tr:ae (A.op L.op)
                  -> a:A.s L.s
                  -> b:A.s L.s
                  -> Lemma (requires (A.sim_a #L.s #L.op #L.rval tr a /\ A.sim_a #L.s #L.op #L.rval tr b))
                          (ensures (forall e. A.mem_key_s e a <==> A.mem_key_s e b) /\
                                   (forall ch. A.mem_key_s ch a /\ A.mem_key_s ch b ==> 
                                   (A.get_val_s #L.s #L.op #L.rval ch a) = (A.get_val_s #L.s #L.op #L.rval ch b)))

#set-options "--z3rlimit 1000"
let convergence_a tr a b = 
  A.convergence_a1 #L.s #L.op #L.rval  tr a b;
  convergence2 tr a b;
  lem_length a b (A.get_lst a);
  convergence3 a b (A.get_lst a)

val prop_merge_a : ltr:ae (A.op L.op)
            -> l:(A.s L.s)
            -> atr:ae (A.op L.op)
            -> a:(A.s L.s)
            -> btr:ae (A.op L.op)
            -> b:(A.s L.s)
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (A.sim_a #L.s #L.op #L.rval ltr l /\ 
                              A.sim_a #L.s #L.op #L.rval (union ltr atr) a /\
                              A.sim_a #L.s #L.op #L.rval (union ltr btr) b) /\
                              pre_cond_merge_a l a b /\
                             (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                (pre_cond_prop_merge #L.s #L.op #L.rval (A.project ch ltr) (A.get_val_s #L.s #L.op #L.rval ch l)
                                                        (A.project ch atr) (A.get_val_s #L.s #L.op #L.rval ch a)
                                                        (A.project ch btr) (A.get_val_s #L.s #L.op #L.rval ch b)) /\
                (sim #L.s #L.op #L.rval (A.project ch ltr) (A.get_val_s #L.s #L.op #L.rval ch l) /\ sim #L.s #L.op #L.rval (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #L.s #L.op #L.rval ch a) /\ sim #L.s #L.op #L.rval (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #L.s #L.op #L.rval ch b))))
                (ensures (A.sim_a #L.s #L.op #L.rval (abs_merge ltr atr btr) (merge_a l a b)))

#set-options "--z3rlimit 1000"
let prop_merge_a ltr l atr a btr b = 
  A.prop_merge_a #L.s #L.op #L.rval #L.log ltr l atr a btr b

val extract : r:L.rval {r <> L.Bot} -> L.s
let extract (L.Val s) = s

val spec_a : o1:(nat * (A.op L.op))
           -> tr:ae (A.op L.op)
           -> Pure L.rval
             (requires true)
             (ensures (fun res -> A.opget o1 ==> (res = L.spec (A.project_op o1) (A.project (A.get_key o1) tr))))
let spec_a o1 tr = L.spec (A.project_op o1) (A.project (A.get_key o1) tr)

val prop_spec_a : tr:ae (A.op L.op)
                  -> st1:(A.s L.s)
                  -> op:(nat * (A.op L.op))
                  -> Lemma (requires (A.sim_a #L.s #L.op #L.rval tr st1) /\ (not (mem_id (get_id op) tr.l)) /\
                                    (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0 /\
                                    pre_cond_do_a st1 op)
                    (ensures A.opget op ==> (get_rval (A.do_a #L.s #L.op #L.rval st1 op)) =
                                                  ((A.spec_a #L.s #L.op #L.rval) op tr))

#set-options "--z3rlimit 1000"
let prop_spec_a tr st op =
  L.prop_spec (A.project (A.get_key op) tr) (A.get_val_s #L.s #L.op #L.rval (A.get_key op) st) (A.project_op op)

val sim_a : tr:ae (A.op L.op)
          -> s1:(A.s L.s)
          -> Tot (b:bool {(b = true) <==> (forall e1. mem e1 s1 ==> (exists e. mem e tr.l /\ A.get_key_s e1 = A.get_key e /\ A.opset e)) /\
                (forall k. A.mem_key_s k s1 ==> L.sim (A.project k tr) (A.get_val_s #L.s #L.op #L.rval k s1)) /\
              (forall e. mem e tr.l /\ A.opset e ==> (exists e1. mem e1 s1 /\ A.get_key e = A.get_key_s e1))})
let sim_a tr s1 = A.sim_a #L.s #L.op #L.rval tr s1

instance log_map : mrdt (A.s L.s) (A.op L.op) (L.rval) = {
  Library.init = A.init_a;
  Library.spec = spec_a;
  Library.sim = sim_a;
  Library.pre_cond_do = pre_cond_do_a;
  Library.pre_cond_prop_do = pre_cond_prop_do_a;
  Library.pre_cond_merge = pre_cond_merge_a;
  Library.pre_cond_prop_merge = pre_cond_prop_merge_a;
  Library.do = A.do_a;
  Library.merge = merge_a;
  Library.prop_do = prop_do_a;
  Library.prop_merge = prop_merge_a;
  Library.prop_spec = prop_spec_a;
  Library.convergence = convergence_a
}
