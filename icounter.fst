module ICounter

open FStar.List.Tot

type state = nat

type operation =
  | Inc : nat -> operation

type trace = list operation

val apply_op : operation -> state -> nat
let apply_op (Inc n) s = s + n

let rec apply_tr t s =
  match t with
  | [] -> s
  | op::ops -> apply_tr ops (apply_op op s)

val lem_trans : a:state
           -> t0:trace
           -> b:state{apply_tr t0 a = b}
           -> t1:trace
           -> c:state{apply_tr t1 b = c}
           -> Lemma (ensures (apply_tr (append t0 t1) a = c)) (decreases %[t0;t1])
let rec lem_trans a t0 b t1 c = match t0 with
| [] -> ()
| op::ops -> lem_trans (apply_op op a) ops b t1 c

val concat_trace : a:state
                -> t0:trace
                -> b:state{apply_tr t0 a = b}
                -> t1:trace
                -> c:state{apply_tr t1 b = c}
                -> t:trace{t = append t0 t1 /\ apply_tr t a = c}
let concat_trace a t0 b t1 c = 
  lem_trans a t0 b t1 c;
  append t0 t1

val lem_monotonic_increase : t:trace 
                           -> inp:state 
                           -> Lemma (ensures (apply_tr t inp >= inp))
let rec lem_monotonic_increase t inp = 
  match t with
  | [] -> ()
  | op::ops -> lem_monotonic_increase ops (apply_op op inp)

val merge_trace : lca:state
                -> t0:trace
                -> a:state{apply_tr t0 lca = a}
                -> t1:trace
                -> b:state{apply_tr t1 lca = b}
                -> trace
let merge_trace lca t0 a t1 b =
  lem_monotonic_increase t0 lca;
  lem_monotonic_increase t1 lca;
  [Inc (a - lca + b - lca)]

val merge : lca:state
          -> t0:list operation
          -> a:state{apply_tr t0 lca = a}
          -> t1:list operation
          -> b:state{apply_tr t1 lca = b}
          -> m:state{m = apply_tr (merge_trace lca t0 a t1 b) lca}
let merge lca t0 a t1 b =
  lem_monotonic_increase t0 lca;
  assert(a >= lca);
  a + b - lca

val commutativity : lca:state
                  -> t0:list operation
                  -> a:state{apply_tr t0 lca = a}
                  -> t1:list operation
                  -> b:state{apply_tr t1 lca = b}
                  -> Lemma (ensures (merge lca t0 a t1 b) = (merge lca t1 b t0 a))
let commutativity lca t0 a t1 b = ()


val associativity : l0:state
                  -> t0:list operation
                  -> l1:state{apply_tr t0 l0 = l1}
                  -> t1:list operation
                  -> a:state{apply_tr t1 l1 = a}
                  -> t2:list operation
                  -> b:state{apply_tr t2 l1 = b}
                  -> t3:list operation
                  -> c:state{apply_tr t3 l0 = c}
                  -> Lemma (ensures (merge l0 (concat_trace l0 t0 l1 (merge_trace l1 t1 a t2 b) (merge l1 t1 a t2 b)) (merge l1 t1 a t2 b) t3 c =
                                    merge l1 t1 a (merge_trace l0 (concat_trace l0 t0 l1 t2 b) b t3 c) (merge l0 (concat_trace l0 t0 l1 t2 b) b t3 c)))
let associativity l0 t0 l1 t1 a t2 b t3 c = ()
