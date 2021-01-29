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

val merge : h:history s o{wellformed h}
          -> a:history s o{hbeq h a}
          -> b:history s o{hbeq h b}
          -> l:history s o{lca h a b = [l]}
          -> s
let merge h a b l = 
  History.lemma1 h;
  assert (wellformed a);
  assert (wellformed l);

  let tr = get_trace l a in
  assert (fold_left apply_op (get_state l) tr = get_state a);

  lemma1 tr (get_state l);
  assert (get_state a >= get_state l);

  get_state a + get_state b - get_state l

val commutativity : h:history s o{wellformed h}
                  -> a:history s o{hbeq h a}
                  -> b:history s o{hbeq h b}
                  -> l:history s o{lca h a b = [l] /\ lca h b a = [l]}
                  -> Lemma (ensures (merge h a b l = merge h b a l))
let commutativity h a b l = ()

instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity
}
