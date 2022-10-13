module Ictr

open FStar.List.Tot
open FStar.Ghost
open FStar.Seq.Base
open FStar.Seq.Properties

type op =
  | Inc

type ctr_st = nat //concrete state of the counter
type st = ctr_st & (erased (Seq.seq (ctr_st & (nat (*id*) & op))))

val init : st
let init = (0, hide empty)

val get_id : (nat * op) -> nat
let get_id (id, o) = id

let get_op (_, o) = o

val get_val : st -> ctr_st
let get_val (c, _) = c

val get_seq : st -> GTot (Seq.seq (ctr_st * (nat * op)))
let get_seq (st, seq) = (reveal seq)

val get_st : (ctr_st * (nat * op)) -> ctr_st
let get_st (st, o) = st

val get_init : c:st -> GTot nat
let get_init c = 
  if (length (get_seq c) > 0) then get_st (head (get_seq c)) else get_val c

val last_op : c:st{length (get_seq c) > 0} -> GTot (nat * op)
let last_op c = get_op (last (get_seq c))

val inverse : c:st{length (get_seq c) > 0} -> GTot ctr_st
let inverse c = get_st (last (get_seq c))

val st_i : c:st{length (get_seq c) > 0} -> i:nat{i < length (get_seq c)} -> GTot ctr_st
let st_i c i = (get_st (index (get_seq c) i))

val op_i : c:st{length (get_seq c) > 0} -> i:nat{i < length (get_seq c)} -> GTot (nat * op)
let op_i c i = (get_op (index (get_seq c) i))

let pre_cond_do s op = true 

val do : c:ctr_st -> (nat * op) -> c1:ctr_st{c1 > c}
let do c (_, Inc) = c + 1

let valid_st (c:st) = 
  (forall i. i < length (get_seq c) - 1 ==> do (st_i c i) (op_i c i) = (st_i c (i+1))) /\
  (length (get_seq c) > 0 ==> get_val c = do (inverse c) (last_op c))

val lemma1 : c:st
           -> Lemma (requires valid_st c /\ length (get_seq c) > 0)
                   (ensures get_init c <= inverse c)
                   (decreases (length (get_seq c)))
let rec lemma1 c =
  match (length (get_seq c)) with
  |0 -> ()
  |1 -> ()
  |_ -> lemma1 (inverse c, hide (slice (get_seq c) 0 (length (get_seq c) - 1)))

val pre_cond_merge : l:ctr_st -> a:ctr_st -> b:ctr_st -> bool
let pre_cond_merge l a b = a >= l && b >= l

val merge : l:ctr_st -> a:ctr_st -> b:ctr_st
           -> Pure ctr_st (requires pre_cond_merge l a b)
                    (ensures (fun r -> r = a + b - l))
let merge l a b =
  a + b - l

//equivalence relation between 2 states
val eq_m : a:ctr_st -> b:ctr_st -> bool
let eq_m a b = a = b

val prop_merge1 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) > 0 /\ length (get_seq b) > 0 /\
                                  get_init a = get_init b /\ get_init a = get_val l /\ 
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                         (ensures pre_cond_merge (get_val l) (inverse a) (inverse b) /\
                                  (let m = merge (get_val l) (inverse a) (inverse b) in
                                       eq_m (merge (get_val l) (get_val a) (get_val b)) 
                                            (merge m (do m (last_op a)) (do m (last_op b)))))
let prop_merge1 l a b = 
  lemma1 a;
  lemma1 b

val prop_merge2 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) = 0 /\ length (get_seq b) > 0 /\
                                  get_val a = get_init b /\ get_val a = get_val l /\
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                        (ensures pre_cond_merge (get_val l) (get_val a) (inverse b) /\
                                 (let m = merge (get_val l) (get_val a) (inverse b) in
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) (do m (last_op b))))
let prop_merge2 l a b = 
  lemma1 b

val prop_merge3 : l:st -> a:st -> b:st
                -> Lemma (requires valid_st l /\ valid_st a /\ valid_st b /\ 
                                  length (get_seq a) > 0 /\ length (get_seq b) = 0 /\
                                  get_val b = get_init a /\ get_val b = get_val l /\
                                  pre_cond_merge (get_val l) (get_val a) (get_val b))
                        (ensures pre_cond_merge (get_val l) (inverse a) (get_val b) /\
                                 (let m = merge (get_val l) (inverse a) (get_val b) in
                                      eq_m (merge (get_val l) (get_val a) (get_val b)) (do m (last_op a))))
let prop_merge3 l a b = 
  lemma1 a

val spec : nat -> (nat * op) -> (nat * op) -> nat
let spec a o1 o2 =
  do (do a o1) o2

val lem_spec : l:st -> a:st -> b:st
             -> o1:(nat * op) -> o2:(nat * op)
             -> Lemma (requires pre_cond_do (get_val l) o1 /\ pre_cond_do (get_val l) o2 /\ get_id o1 <> get_id o2 /\
                               get_val a = do (get_val l) o1 /\ get_val b = do (get_val l) o2)
                     (ensures pre_cond_merge (get_val l) (get_val a) (get_val b) /\ 
                              eq_m (spec (get_val l) o1 o2) (merge (get_val l) (get_val a) (get_val b)))
let lem_spec l a b o1 o2 = ()

