module Log_map
open FStar.List.Tot

open Library
open FStar.Tactics.Typeclasses

module A = Alpha_map

module G = Log

val pre_cond_merge1_a1 : l:A.s G.s -> a:A.s G.s -> b:A.s G.s 
                      -> Pure bool
                        (requires true)
                        (ensures (fun b1 -> (b1 = true <==> (forall e. A.mem_key_s e l ==> A.mem_key_s e a /\ A.mem_key_s e b) /\
                        (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                                       (forall e. mem e (A.get_val_s #G.s #G.op ch l) ==> mem e (A.get_val_s #G.s #G.op ch a) /\ mem e (A.get_val_s #G.s #G.op ch b)) /\
                      (forall e e1. mem e (A.get_val_s #G.s #G.op ch l) /\ mem e1 (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch l)) ==> G.fst e1 > G.fst e) /\
                      (forall e e1. mem e (A.get_val_s #G.s #G.op ch l) /\ mem e1 (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)) ==> G.fst e1 > G.fst e)))))

#set-options "--z3rlimit 10000000"
let pre_cond_merge1_a1 l a b =
  forallb (fun e -> A.mem_key_s (A.get_key_s #G.s e) a && A.mem_key_s (A.get_key_s #G.s e) b) l &&
  forallb (fun ch -> (forallb (fun e -> mem e (A.get_val_s #G.s #G.op ch a) && mem e (A.get_val_s #G.s #G.op ch b)) (A.get_val_s #G.s #G.op ch l)) &&
            (forallb (fun e -> (forallb (fun e1 -> G.fst e1 > G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch l)))) (A.get_val_s #G.s #G.op ch l)) &&
            (forallb (fun e -> (forallb (fun e1 -> G.fst e1 > G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)))) (A.get_val_s #G.s #G.op ch l))) (A.get_key_lst l a b)

val pre_cond_merge1_a2 : l:A.s G.s -> a:A.s G.s -> b:A.s G.s 
                      -> Pure bool
                        (requires true)
                        (ensures (fun b1 -> (b1 = true <==> (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                                           (G.pre_cond_merge1 (A.get_val_s #G.s #G.op ch l) 
                                           (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b)) /\
                        (forall e. mem e (A.get_val_s #G.s #G.op ch l) ==> mem e (A.get_val_s #G.s #G.op ch a) /\ mem e (A.get_val_s #G.s #G.op ch b)) /\
                          (forall e. mem e (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch l)) ==>
                      not (G.mem_id_s (G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)))) /\
                      (forall e. mem e (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)) ==>
                                                         not (G.mem_id_s (G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s#G.s #G.op  ch l))))))))

#set-options "--z3rlimit 10000000"
let pre_cond_merge1_a2 l a b =
  forallb (fun ch -> G.pre_cond_merge1 (A.get_val_s #G.s #G.op ch l) (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b) &&
            (forallb (fun e -> mem e (A.get_val_s #G.s #G.op ch a) && mem e (A.get_val_s #G.s #G.op ch b)) (A.get_val_s #G.s #G.op ch l)) &&

            (forallb (fun e -> not (G.mem_id_s (G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)))) (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch l))) &&
            (forallb (fun e -> not (G.mem_id_s (G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s#G.s #G.op  ch l)))) (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)))) (A.get_key_lst l a b)

val pre_cond_merge1_a : l:A.s G.s -> a:A.s G.s -> b:A.s G.s 
                      -> Pure bool
                        (requires true)
                        (ensures (fun b1 -> (b1 = true <==> (forall e. A.mem_key_s e l ==> A.mem_key_s e a /\ A.mem_key_s e b) /\
                        (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                                           (G.pre_cond_merge1 (A.get_val_s #G.s #G.op ch l) 
                                           (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b)) /\
                        (forall e. mem e (A.get_val_s #G.s #G.op ch l) ==> mem e (A.get_val_s #G.s #G.op ch a) /\ mem e (A.get_val_s #G.s #G.op ch b)) /\
                          (forall e. mem e (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch l)) ==>
                      not (G.mem_id_s (G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)))) /\
                      (forall e. mem e (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)) ==>
                                                         not (G.mem_id_s (G.fst e) (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s#G.s #G.op  ch l)))) /\
                      (forall e e1. mem e (A.get_val_s #G.s #G.op ch l) /\ mem e1 (G.diff_s (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch l)) ==> G.fst e1 > G.fst e) /\
                      (forall e e1. mem e (A.get_val_s #G.s #G.op ch l) /\ mem e1 (G.diff_s (A.get_val_s #G.s #G.op ch b) (A.get_val_s #G.s #G.op ch l)) ==> G.fst e1 > G.fst e)))))

#set-options "--z3rlimit 10000000"
let pre_cond_merge1_a l a b =
  pre_cond_merge1_a1 l a b &&
  pre_cond_merge1_a2 l a b

val merge2 : l:A.s G.s -> a:A.s G.s -> b:A.s G.s 
           -> lst:list nat
           -> Pure (A.s G.s)
             (requires pre_cond_merge1_a l a b /\ A.unique_keys lst /\
                       (forall ch. mem ch lst ==> A.mem_key_s ch a \/ A.mem_key_s ch b))
             (ensures (fun r -> (forall ch. A.mem_key_s ch r <==> mem ch lst) /\ A.unique_key r /\
                             (forall ch. mem ch lst ==> (A.get_val_s #G.s #G.op ch r) =
                             (G.merge1 (A.get_val_s #G.s #G.op ch l) (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b)))))
                (decreases lst)

#set-options "--z3rlimit 10000000"
let rec merge2 l a b lst =
  match lst with
  |[] -> []
  |x::xs -> (x, G.merge1 (A.get_val_s #G.s #G.op x l) (A.get_val_s #G.s #G.op x a) (A.get_val_s #G.s #G.op x b))::merge2 l a b xs

val merge1_a : l:A.s G.s
             -> a:A.s G.s
             -> b:A.s G.s
             -> Pure (A.s G.s)
               (requires pre_cond_merge1_a l a b)
               (ensures (fun r -> (forall ch. A.mem_key_s ch r <==> A.mem_key_s ch a \/ A.mem_key_s ch b) /\ A.unique_key r /\
                               (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> (A.get_val_s #G.s #G.op ch r) =
                               (G.merge1 (A.get_val_s #G.s #G.op ch l) (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b)))))

let merge1_a l a b = 
  let lst = A.get_key_lst l a b in
  merge2 l a b lst

val lemma2 : s1:A.s G.s
           -> Lemma (requires true)
                   (ensures (forall e. mem e s1 ==> (A.get_val_s #G.s #G.op (A.get_key_s e) s1 = A.get_val_s1 #G.s e)))
let rec lemma2 s1 =
  match s1 with
  |[] -> ()
  |x::xs -> lemma2 xs

val lemma4 : tr:ae (A.op G.op) -> s1:A.s G.s
           -> Lemma (requires A.sim_a tr s1)
                   (ensures (forall i. (G.sim (A.project i tr) (A.get_val_s #G.s #G.op i s1))))
let lemma4 tr s1 = ()

val lemma1 : tr:ae (A.op G.op)
         -> st:A.s G.s
         -> op1:(nat * (A.op G.op))
         -> Lemma (requires (A.sim_a tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                           (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                           G.pre_cond_op (A.get_val_s #G.s #G.op (A.get_key op1) st) (A.project_op op1))
                 (ensures (forall i. A.mem_key_s i (A.app_op_a st op1) /\ i <> A.get_key op1 ==>
                 ((forall e. mem e (A.project i (append tr op1)).l <==> mem e (A.project i tr).l) /\
             (forall e e1. mem e (A.project i (append tr op1)).l /\ mem e1 (A.project i (append tr op1)).l /\ get_id e <> get_id e1 /\
                      (A.project i (append tr op1)).vis e e1 <==> 
                 mem e (A.project i tr).l /\ mem e1 (A.project i tr).l /\ get_id e <> get_id e1 /\ (A.project i tr).vis e e1) /\
                   (A.get_val_s #G.s #G.op i (A.app_op_a st op1) = (A.get_val_s #G.s #G.op i st))) ==>
                     (G.sim (A.project i (append tr op1)) (A.get_val_s #G.s #G.op i (A.app_op_a st op1)))))

#set-options "--z3rlimit 10000000"
let lemma1 tr st op = ()

val lemma7 : tr:ae G.op -> s1:G.s -> tr1:ae G.op
           -> Lemma (requires G.sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                             (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                      mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                   (ensures (G.sim tr1 s1))
#set-options "--z3rlimit 10000000"
let lemma7 tr s1 tr1 = ()

val pre_cond_merge_a : ltr:ae (A.op G.op) 
                     -> l:A.s G.s 
                     -> atr:ae (A.op G.op)
                     -> a:A.s G.s 
                     -> btr:ae (A.op G.op)
                     -> b:A.s G.s
                     -> Tot (b1:bool {b1=true <==> (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==>
                          (G.pre_cond_merge (A.project ch ltr) (A.get_val_s #G.s #G.op ch l)
                                            (A.project ch atr) (A.get_val_s #G.s #G.op ch a)
                                            (A.project ch btr) (A.get_val_s #G.s #G.op ch b)) /\
                              (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch atr).l)) /\
                              (forall e. mem e (A.project ch atr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                              (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                              (G.sim (A.project ch ltr) (A.get_val_s #G.s #G.op ch l) /\ 
                           G.sim (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #G.s #G.op ch a) /\
                  G.sim (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #G.s #G.op ch b)))})

let pre_cond_merge_a ltr l atr a btr b = 
    forallb (fun ch -> (G.pre_cond_merge (A.project ch ltr) (A.get_val_s #G.s #G.op ch l)
                                      (A.project ch atr) (A.get_val_s #G.s #G.op ch a)
                                      (A.project ch btr) (A.get_val_s #G.s #G.op ch b)) &&
                    (forallb (fun e -> not (mem_id (get_id e) (A.project ch atr).l)) (A.project ch ltr).l) &&
                    (forallb (fun e -> not (mem_id (get_id e) (A.project ch btr).l)) (A.project ch atr).l) &&
                    (forallb (fun e -> not (mem_id (get_id e) (A.project ch btr).l)) (A.project ch ltr).l) &&
                    (G.sim (A.project ch ltr) (A.get_val_s #G.s #G.op ch l)) &&
                    (G.sim (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #G.s #G.op ch a)) &&
                    (G.sim (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #G.s #G.op ch b)))
             (A.get_key_lst l a b)

val merge_a : ltr:ae (A.op G.op)
          -> l:A.s G.s
          -> atr:ae (A.op G.op)
          -> a:A.s G.s
          -> btr:ae (A.op G.op)
          -> b:A.s G.s
          -> Pure (A.s G.s) (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (A.sim_a ltr l /\ A.sim_a (union ltr atr) a /\ A.sim_a (union ltr btr) b) /\
                             pre_cond_merge1_a l a b /\ pre_cond_merge_a ltr l atr a btr b)
                 (ensures (fun r -> (forall i. A.mem_key_s i l ==> A.mem_key_s i a /\ A.mem_key_s i b) /\
                                 (forall i. A.mem_key_s i r <==> A.mem_key_s i a \/ A.mem_key_s i b) /\
                               (forall ch. A.mem_key_s ch r ==> (A.get_val_s #G.s #G.op ch r) =
      (G.merge1 (A.get_val_s #G.s #G.op ch l) (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b))) /\
                             (forall ch. A.mem_key_s ch r ==> (A.get_val_s #G.s #G.op ch r) =
                        (G.merge (A.project ch ltr) (A.get_val_s #G.s #G.op ch l) (A.project ch atr) (A.get_val_s #G.s #G.op ch a) (A.project ch btr) (A.get_val_s #G.s #G.op ch b))) /\
                        (r = merge1_a l a b)))

#set-options "--z3rlimit 10000000"
let merge_a ltr l atr a btr b = 
  let keys = A.get_key_lst l a b in
  A.lem_merge1 ltr l atr a btr b keys;
  let r = merge1_a l a b in
  r

instance _ : A.alpha_map (G.s) (G.op) G.log = {
    A.lemma1 = lemma1;
    A.lemma4 = lemma4;
    A.lemma2 = lemma2;
    A.lemma7 = lemma7
}

val prop_oper : tr:ae (A.op G.op)
              -> st:A.s G.s
              -> op1:(nat * (A.op G.op)) 
              -> Lemma (requires (A.sim_a tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                A.pre_cond_op_a st op1)
                      (ensures (A.sim_a (append tr op1) (A.app_op_a st op1)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op = 
  assert (G.pre_cond_op (A.get_val_s #G.s #G.op (A.get_key op) st) (A.project_op op));
  G.prop_oper (A.project (A.get_key op) tr) (A.get_val_s #G.s #G.op (A.get_key op) st) (A.project_op op); 
  assert (G.sim (append (A.project (A.get_key op) tr) (A.project_op op)) (G.app_op (A.get_val_s #G.s #G.op (A.get_key op) st) (A.project_op op)));
  A.lem_oper tr op;
  assert (G.app_op (A.get_val_s #G.s #G.op (A.get_key op) st) (A.project_op op) =
          A.get_val_s #G.s #G.op (A.get_key op) (A.app_op_a st op));
  assert (G.sim (A.project (A.get_key op) (append tr op)) (A.get_val_s #G.s #G.op (A.get_key op) (A.app_op_a st op)));
  A.prop_oper_a #G.s #G.op #G.log tr st op; ()

val convergence2 : tr:ae (A.op G.op)
                 -> a:(A.s G.s)
                 -> b:(A.s G.s)
                 -> Lemma (requires (A.sim_a tr a /\ A.sim_a tr b))
                         (ensures (forall ch. A.mem_key_s ch a /\ A.mem_key_s ch b ==> 
                             (forall e e1. mem e (A.get_val_s #G.s #G.op ch a) /\ mem e1 (A.get_val_s #G.s #G.op ch a) /\ 
                              G.fst e <> G.fst e1 /\ G.fst e > G.fst e1 /\ G.ord e e1 (A.get_val_s #G.s #G.op ch a)  <==> 
                  mem e (A.get_val_s #G.s #G.op ch b) /\ mem e1 (A.get_val_s #G.s #G.op ch b) /\ G.fst e <> G.fst e1 /\
                                       G.fst e > G.fst e1 /\ G.ord e e1 (A.get_val_s #G.s #G.op ch b))) /\
                                     (forall ch. A.mem_key_s ch a /\ A.mem_key_s ch b ==>
                 (forall e. G.mem_id_s e (A.get_val_s #G.s #G.op ch a) <==> G.mem_id_s e (A.get_val_s #G.s #G.op ch b))))

#set-options "--z3rlimit 100000000"
let convergence2 tr a b = 
  A.convergence_a1 tr a b

val lem_length : a:(A.s G.s)
               -> b:(A.s G.s)
               -> lst:list nat
               -> Lemma (requires (forall ch. mem ch lst ==> A.mem_key_s ch a /\ A.mem_key_s ch b) /\
                                          (forall e. A.mem_key_s e a <==> A.mem_key_s e b) /\
                                    A.unique_keys lst /\ (forall ch. mem ch lst ==> 
                 (forall e. G.mem_id_s e (A.get_val_s #G.s #G.op ch a) <==> G.mem_id_s e (A.get_val_s #G.s #G.op ch b))))
                 (ensures (forall ch. mem ch lst ==> (List.Tot.length (A.get_val_s #G.s #G.op ch a) = List.Tot.length (A.get_val_s #G.s #G.op ch b))))
                          (decreases lst)

let rec lem_length a b lst =
  match lst with
  |[] -> ()
  |ch::chs -> G.lem_length (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b); lem_length a b chs

val convergence3 : a:(A.s G.s)
                 -> b:(A.s G.s)
                 -> lst:list nat
                   -> Lemma (requires (forall ch. mem ch lst ==> A.mem_key_s ch a /\ A.mem_key_s ch b) /\
                                            (forall e. A.mem_key_s e a <==> A.mem_key_s e b) /\
                                     A.unique_keys lst /\ (forall ch. mem ch lst ==> 
                   (forall e. G.mem_id_s e (A.get_val_s #G.s #G.op ch a) <==> G.mem_id_s e (A.get_val_s #G.s #G.op ch b))) /\
            (forall ch. mem ch lst ==> (forall e. mem e (A.get_val_s #G.s #G.op ch a) <==> mem e (A.get_val_s #G.s #G.op ch b))) /\
                              (forall ch. mem ch lst ==> (List.Tot.length (A.get_val_s #G.s #G.op ch a) = List.Tot.length (A.get_val_s #G.s #G.op ch b))) /\
                         (forall ch. mem ch lst ==> 
                       (forall e e1. mem e (A.get_val_s #G.s #G.op ch a) /\ mem e1 (A.get_val_s #G.s #G.op ch a) /\ 
                         G.fst e <> G.fst e1 /\ G.fst e > G.fst e1 /\ G.ord e e1 (A.get_val_s #G.s #G.op ch a)  <==> 
              mem e (A.get_val_s #G.s #G.op ch b) /\ mem e1 (A.get_val_s #G.s #G.op ch b) /\ G.fst e <> G.fst e1 /\
                          G.fst e > G.fst e1 /\ G.ord e e1 (A.get_val_s #G.s #G.op ch b))))
                     (ensures (forall ch. mem ch lst ==> (A.get_val_s #G.s #G.op ch a = A.get_val_s #G.s #G.op ch b)))
                         (decreases lst)
#set-options "--z3rlimit 10000000"
let rec convergence3 a b lst =
  match lst with
  |[] -> ()
  |ch::chs -> G.lem_same (A.get_val_s #G.s #G.op ch a) (A.get_val_s #G.s #G.op ch b);
            convergence3 a b chs

val convergence_a : tr:ae (A.op G.op)
                  -> a:A.s G.s
                  -> b:A.s G.s
                  -> Lemma (requires (A.sim_a tr a /\ A.sim_a tr b))
                          (ensures (forall e. A.mem_key_s e a <==> A.mem_key_s e b) /\
                                      (forall ch. A.mem_key_s ch a /\ A.mem_key_s ch b ==> 
                               (A.get_val_s #G.s #G.op ch a) = (A.get_val_s #G.s #G.op ch b)))

#set-options "--z3rlimit 100000000"
let convergence_a tr a b = 
  A.convergence_a1 tr a b;
  convergence2 tr a b;
  lem_length a b (A.get_lst a);
  convergence3 a b (A.get_lst a)

val prop_merge_a : ltr:ae (A.op G.op)
          -> l:(A.s G.s)
            -> atr:ae (A.op G.op)
            -> a:(A.s G.s)
            -> btr:ae (A.op G.op)
            -> b:(A.s G.s)
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (A.sim_a ltr l /\ A.sim_a (union ltr atr) a /\ A.sim_a (union ltr btr) b) /\
                             pre_cond_merge1_a l a b /\
                             (forall ch. A.mem_key_s ch a \/ A.mem_key_s ch b ==> 
                             (pre_cond_merge #G.s #G.op (A.project ch ltr) (A.get_val_s #G.s #G.op  ch l)
                                                    (A.project ch atr) (A.get_val_s #G.s #G.op  ch a)
                                                    (A.project ch btr) (A.get_val_s #G.s #G.op  ch b)) /\
                            (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch atr).l)) /\
                            (forall e. mem e (A.project ch atr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                            (forall e. mem e (A.project ch ltr).l ==> not (mem_id (get_id e) (A.project ch btr).l)) /\
                                  (sim #G.s #G.op (A.project ch ltr) (A.get_val_s #G.s #G.op  ch l) /\ sim #G.s #G.op (union (A.project ch ltr) (A.project ch atr)) (A.get_val_s #G.s #G.op  ch a) /\ sim #G.s #G.op (union (A.project ch ltr) (A.project ch btr)) (A.get_val_s #G.s #G.op  ch b))))
                    (ensures (A.sim_a (absmerge ltr atr btr) (merge_a ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge_a ltr l atr a btr b = 
  A.prop_merge_a #G.s #G.op #G.log ltr l atr a btr b

#set-options "--z3rlimit 10000000" 
instance log_map : mrdt (A.s G.s) (A.op G.op) = {
  Library.init = A.init_a;
  Library.sim = A.sim_a;
  Library.pre_cond_op = A.pre_cond_op_a;
  Library.app_op = A.app_op_a;
  Library.prop_oper = prop_oper;
  Library.pre_cond_merge1 = pre_cond_merge1_a;
  Library.pre_cond_merge = pre_cond_merge_a;
  Library.merge1 = merge1_a;
  Library.merge = merge_a;
  Library.prop_merge = prop_merge_a;
  Library.convergence = convergence_a;
}
