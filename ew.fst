module Ew

open FStar.List.Tot
open FStar.Ghost
open FStar.Seq.Base
open FStar.Seq.Properties

type op =
  |Enable
  |Disable

type ew_st = nat & bool //concrete state of the enable-wins flag
type st = ew_st & (erased (Seq.seq (ew_st & (nat (*id*) & op))))

val init : st
let init = ((0, false), hide empty)

val get_id : (nat * op) -> nat
let get_id (id, o) = id

let get_op (_, o) = o

val get_val : st -> ew_st
let get_val (c, _) = c

val get_seq : st -> GTot (Seq.seq (ew_st * (nat * op)))
let get_seq (st, seq) = (reveal seq)

val get_st : (ew_st * (nat * op)) -> ew_st
let get_st (st, o) = st

val get_init : c:st -> GTot ew_st
let get_init c = 
  if (length (get_seq c) > 0) then get_st (head (get_seq c)) else get_val c

val last_op : c:st{length (get_seq c) > 0} -> GTot (nat * op)
let last_op c = get_op (last (get_seq c))

val inverse : c:st{length (get_seq c) > 0} -> GTot ew_st
let inverse c = get_st (last (get_seq c))

val st_i : c:st{length (get_seq c) > 0} -> i:nat{i < length (get_seq c)} -> GTot ew_st
let st_i c i = (get_st (index (get_seq c) i))

val op_i : c:st{length (get_seq c) > 0} -> i:nat{i < length (get_seq c)} -> GTot (nat * op)
let op_i c i = (get_op (index (get_seq c) i))

let pre_cond_do s op = true 

val do : st:ew_st -> o:(nat * op) -> st1:ew_st{(get_op o = Enable <==> (st1 = (fst st + 1, true))) /\
                                           (get_op o = Disable <==> (st1 = (fst st, false)))}
let do s' op =
  match op with
  |(_,Enable) -> (fst s' + 1, true)
  |(_,Disable) -> (fst s', false)

let valid_st (c:st) = 
  (forall i. i < length (get_seq c) - 1 ==> do (st_i c i) (op_i c i) = (st_i c (i+1))) /\
  (length (get_seq c) > 0 ==> get_val c = do (inverse c) (last_op c))

val lemma1 : c:st
           -> Lemma (requires valid_st c /\ length (get_seq c) > 0)
                   (ensures fst (get_init c) <= fst (inverse c))
                   (decreases (length (get_seq c)))
let rec lemma1 c =
  match (length (get_seq c)) with
  |0 -> ()
  |1 -> ()
  |_ -> lemma1 (inverse c, hide (slice (get_seq c) 0 (length (get_seq c) - 1)))

val pre_cond_merge : l:ew_st -> a:ew_st -> b:ew_st -> bool
let pre_cond_merge l a b = fst a >= fst l && fst b >= fst l

val merge_flag : l:ew_st
               -> a:ew_st{fst a >= fst l}
               -> b:ew_st{fst b >= fst l}
               -> Tot (b1:bool {(b1 = true <==> (snd a = true /\ snd b = true) \/ 
                                             (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                             (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                                (b1 = false <==> (snd a = false /\ snd b = false) \/ 
                                               (snd a = true /\ snd b = false /\ fst a = fst l) \/
                                               (snd b = true /\ snd a = false /\ fst b = fst l))})
let merge_flag l a b =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
    if af && bf then true
      else if not af && not bf then false
        else if af then ac - lc > 0
          else bc - lc > 0

val merge : l:ew_st
          -> a:ew_st
          -> b:ew_st
          -> Pure ew_st (requires pre_cond_merge l a b)
                       (ensures (fun r -> r = (fst a + fst b - fst l, merge_flag l a b)))
let merge l a b =
  let c = fst a + fst b - fst l in
  let f = merge_flag l a b in
  c, f

//equivalence relation between 2 states
val eq_m : a:ew_st -> b:ew_st -> bool
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

val spec : (nat * bool) -> (nat * op) -> (nat * op) -> (nat * bool)
let spec a o1 o2 =
  match o1, o2 with
  |(_, Enable), (_, Disable) -> do (do a o2) o1
  |_ -> do (do a o1) o2

val lem_spec : l:st -> a:st -> b:st
             -> o1:(nat * op) -> o2:(nat * op)
             -> Lemma (requires pre_cond_do (get_val l) o1 /\ pre_cond_do (get_val l) o2 /\ get_id o1 <> get_id o2 /\
                               get_val a = do (get_val l) o1 /\ get_val b = do (get_val l) o2)
                     (ensures pre_cond_merge (get_val l) (get_val a) (get_val b) /\ 
                              eq_m (spec (get_val l) o1 o2) (merge (get_val l) (get_val a) (get_val b)))
let lem_spec l a b o1 o2 = ()





