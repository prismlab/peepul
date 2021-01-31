module Icounter

open FStar.List.Tot
open History

type o =
  | Inc : nat -> o

type s = nat

val app_op : s -> o -> s
let app_op s (Inc n) = s + n

instance icounter : datatype s o = {
  History.apply_op = app_op
}

val le : nat -> nat -> bool
let le a b = a <= b

val lemma1 : tr:list o -> s1:s
           -> Lemma (ensures (le s1 (fold_left apply_op s1 tr)))
let rec lemma1 tr s1 =
  match tr with
  | [] -> ()
  | op::ops ->
     let s2 = app_op s1 op in
     lemma1 ops s2

val lemma2 : l:s -> a:s{a >= l} -> b:s{b >= l} -> c:s{c >= l} 
           -> Lemma (ensures ((a + b - l) + c - l) = (a + (b + c - l) - l))
let lemma2 l a b c = ()

val lemma3 : l1:s -> l2:s -> a:s{a >= l1} -> b:s{b >= l1 /\ b >= l2} -> c:s{c >= l2}
           -> Lemma (ensures ((a + b - l1) + c - l2) = (a + (b + c - l2) - l1))
let lemma3 l1 l2 a b c = ()

val merge : h:history s o{wellformed h}
          -> a:history s o{hbeq h a}
          -> b:history s o{hbeq h b}
          -> l:history s o{lca h a b = [l]}
          -> m:history s o
let merge h a b l = 
  History.lemma1 h;
  assert (wellformed a);
  assert (wellformed l);

  let tr = get_trace l a in
  assert (fold_left apply_op (get_state l) tr = get_state a);

  lemma1 tr (get_state l);
  assert (get_state a >= get_state l);

  (HistLeaf 0 (get_state a + get_state b - get_state l))

val commutativity : h:history s o{wellformed h}
                  -> a:history s o{hbeq h a}
                  -> b:history s o{hbeq h b}
                  -> l:history s o{lca h a b = [l] /\ lca h b a = [l]}
                  -> Lemma (ensures (get_state (merge h a b l) = get_state (merge h b a l)))
let commutativity h a b l = ()

val idempotence : h:history s o{wellformed h}
                -> a:history s o{hbeq h a}
                -> Lemma (requires (lca h a a = [a]))
                        (ensures  (get_state (merge h a a a) = get_state a))
let idempotence h a = ()

val associativity : h:history s o{wellformed h} 
                  -> a:history s o{hbeq h a} 
                  -> b:history s o{hbeq h b} 
                  -> c:history s o{hbeq h c}
                  -> l1:history s o{lca h a b = [l1]}
                  -> l2:history s o{lca h b c = [l2] }
                  -> Lemma (requires (hbeq h (merge h a b l1)) /\ (hbeq h (merge h b c l2)) /\ 
                                    (lca h (merge h a b l1) c = [l2]) /\ (lca h a (merge h b c l2) = [l1])) 
                          (ensures  (get_state (merge h (merge h a b l1) c l2) = get_state (merge h a (merge h b c l2) l1)))

let associativity h a b c l1 l2 = 
    History.lemma1 h;
    let tr1_a = get_trace l1 a in
    let tr1_b = get_trace l1 b in
    let tr2_b = get_trace l2 b in
    let tr2_c = get_trace l2 c in
    lemma1 tr1_a (get_state l1);
    lemma1 tr1_b (get_state l1);
    lemma1 tr2_b (get_state l2);
    lemma1 tr2_c (get_state l2);
    lemma3 (get_state l1) (get_state l2) (get_state a) (get_state b) (get_state c); ()

instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity;
  History.idempotence = idempotence;
  History.associativity = associativity
}
