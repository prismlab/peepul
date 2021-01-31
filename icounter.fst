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

val merge : a:history s o
          -> b:history s o
          -> l:history s o{wellformed l /\ is_lca l a b}
          -> s
let merge a b l = 
  History.lemma1 l;
  assert (wellformed a);

  let tr = get_trace l a in
  assert (fold_left apply_op (get_state l) tr = get_state a);

  lemma1 tr (get_state l);
  assert (get_state a >= get_state l);

  get_state a + get_state b - get_state l

val commutativity : a:history s o
                  -> b:history s o
                  -> l:history s o{wellformed l /\ is_lca l a b}
                  -> Lemma (ensures (merge a b l = merge b a l))
let commutativity a b l = ()

val idempotence : a:history s o{wellformed a /\ is_lca a a a}
                -> Lemma (ensures (merge a a a = get_state a))
let idempotence a = ()

val associativity : a:history s o
                  -> b:history s o
                  -> c:history s o
                  -> l_ab:history s o{wellformed l_ab /\ is_lca l_ab a b}
                  -> l_bc:history s o{wellformed l_bc /\ is_lca l_bc b c}
                  -> m_ab:history s o{merge_node a b m_ab /\ get_state m_ab = merge a b l_ab}
                  -> m_bc:history s o{merge_node b c m_bc /\ get_state m_bc = merge b c l_bc}
                  -> m_ab_c:history s o{merge_node m_ab c m_ab_c}
                  -> m_a_bc:history s o{merge_node a m_bc m_a_bc}
                  -> Lemma (requires (is_lca l_bc m_ab c /\ is_lca l_ab a m_bc /\
                                     get_state m_ab_c = merge m_ab c l_bc /\
                                     get_state m_a_bc = merge a m_bc l_ab))
                          (ensures (get_state m_ab_c = get_state m_a_bc))
let associativity a b c l_ab l_bc m_ab m_bc m_ab_c m_a_bc = ()

instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity;
  History.idempotence = idempotence;
  History.associativity = associativity
}
