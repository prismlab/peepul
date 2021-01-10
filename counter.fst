module Counter

open FStar.List.Tot

type state = nat

type operation =
  | Inc : nat -> operation
  | Dec : nat -> operation

val apply_op : operation -> state -> nat
let apply_op op s =
  match op with
  | Inc n -> s + n
  | Dec n -> if s - n >= 0 then s - n else 0

let rec apply_tr t s =
  match t with
  | [] -> s
  | op::ops -> apply_tr ops (apply_op op s)

val lemma2 : a:state
           -> t0:list operation
           -> b:state{apply_tr t0 a = b}
           -> t1:list operation
           -> c:state{apply_tr t1 b = c}
           -> Lemma (ensures (apply_tr (append t0 t1) a = c)) (decreases %[t0;t1])
let rec lemma2 a t0 b t1 c = match t0 with
| [] -> ()
| op::ops -> lemma2 (apply_op op a) ops b t1 c

val merge : lca:state
          -> a:state
          -> b:state
          -> m:state
let merge lca a b =
  let res = a + b - lca in
  if res >= 0 then res else 0

val merge_trace : lca:state
                 -> t0:list operation
                 -> a:state{apply_tr t0 lca = a}
                 -> t1:list operation
                 -> b:state{apply_tr t1 lca = b}
                 -> t:list operation{apply_tr t lca = merge lca a b}
let merge_trace lca t0 a t1 b =
  if merge lca a b > lca
  then [Inc (merge lca a b - lca)]
  else [Dec (lca - merge lca a b)]

val commutativity : lca:state
                  -> t0:list operation
                  -> a:state{apply_tr t0 lca = a}
                  -> t1:list operation
                  -> b:state{apply_tr t1 lca = b}
                  -> Lemma (ensures (merge lca a b) = (merge lca b a))
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
                  -> Lemma (ensures (merge l0 (merge l1 a b) c = merge l1 a (merge l0 b c)))
let associativity l0 t0 l1 t1 a t2 b t3 c =
  (* left *)
  let ab = merge l1 a b in
  let t_ab = merge_trace l1 t1 a t2 b in
  assert (apply_tr t_ab l1 = ab);


  let ab_c = merge l0 ab c in
  lemma2 l0 t0 l1 t_ab ab;
  assert (apply_tr (append t0 t_ab) l0 = ab);
  let t_ab_c = merge_trace l0 (append t0 t_ab) ab t3 c in
  assert (apply_tr t_ab_c l0 = ab_c);

  (* right *)
  let bc = merge l0 b c in
  lemma2 l0 t0 l1 t2 b;
  assert (apply_tr (append t0 t2) l0 = b);
  let t_bc = merge_trace l0 (append t0 t2) b t3 c in

  let a_bc = merge l0 a bc in
  lemma2 l0 t0 l1 t1 a;
  assert (apply_tr (append t0 t1) l0 = a);
  let t_a_bc = merge_trace l0 (append t0 t1) a t_bc bc in
  assert (apply_tr t_a_bc l0 = a_bc);

  assert (apply_tr t_a_bc l0 = apply_tr t_ab_c l0);
  ()
