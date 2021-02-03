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

val associativity : h:history s o{wellformed h}
                -> a:history s o{wellformed a /\ hbeq h a}
                -> b:history s o{wellformed b /\ hbeq h b}
                -> c:history s o{wellformed c /\ hbeq h c}
                -> lab:history s o{lcau h a b = lab}
                -> lbc:history s o{lcau h b c = lbc}
                -> lac:history s o{lcau h c a = lac}
                -> mab:history s o{hbeq h mab /\ merge_node a b mab /\ get_state mab = merge a b lab}
                -> mbc:history s o{hbeq h mbc /\ merge_node b c mbc /\ get_state mbc = merge b c lbc}
                -> m1:history s o{hbeq h m1 /\ merge_node lab lac m1 /\ get_state m1 = merge lab lac (lcau h lab lac) /\ lcau h a mbc = m1}
                -> m2:history s o{hbeq h m2 /\ merge_node lbc lac m2 /\ get_state m2 = merge lbc lac (lcau h lbc lac) /\ lcau h mab c = m2}
                -> mabc1: history s o{hbeq h mabc1 /\ merge_node a mbc mabc1 /\ get_state mabc1 = merge a mbc m1}
                -> mabc2: history s o{hbeq h mabc2 /\ merge_node mab c mabc2 /\ get_state mabc2 = merge mab c m2}
                -> Lemma (get_state mabc1 = get_state mabc2)
let associativity h a b c lab lbc lac mab mbc m1 m2 mabc1 mabc2 = 
  lcau_associative h a b c lab lbc lac;
  let l2 = lcau h lab lac in
  let l1 = lcau h lbc lac in
  assert (l1 = l2);
  let g = get_state in
  assert (g mab = g a + g b - g lab);
  assert (g mbc = g b + g c - g lbc);
  assert (g mabc1 = g a + g mbc - g m1);
  assert (g a + g b + g c - g lbc - g m1 >= 0);
  assert (g a + (g b + g c - g lbc) - g m1 = g mabc1);
  assert (g m1 = g lab + g lac - g l2);
  assert (g a + (g b + g c - g lbc) - (g lab + g lac - g l2) = g mabc1);
  
  assert (g a + (g b + g c - g lbc) - (g lab + g lac - g l1) = g mabc1);
  assert ((g a + g b - g lab) + g c - (g lbc + g lac - g l1) = g mabc2);
  admit ()

instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity;
  History.idempotence = idempotence;
  History.associativity = associativity
}
