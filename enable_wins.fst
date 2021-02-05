module Enable_wins

open FStar.List.Tot
open History

type o =
  | Enable
  | Disable

type s = nat * bool

val app_op : s -> o -> s
let app_op (c, _) o = 
  match o with
  | Enable -> (c+1, true)
  | Disable -> (c, false)

instance icounter : datatype s o = {
  History.apply_op = app_op
}

val le : nat -> nat -> bool
let le a b = a <= b

val lemma1 : tr:list o -> s1:s
           -> Lemma (ensures (le (fst s1) (fst (fold_left apply_op s1 tr))))
let rec lemma1 tr s1 =
  match tr with
  | [] -> ()
  | op::ops ->
     let s2 = app_op s1 op in
     lemma1 ops s2

val lemma2 : l1:nat -> l2:nat -> lab:nat  -> lbc:nat -> lac:nat  -> a:nat  -> b:nat -> c:nat 
             -> Lemma (requires l1 = l2)
                     (ensures (a + (b + c - lbc) - (lab + lac - l2)) = ((a + b - lab) + c - (lbc + lac - l1)))
let lemma2 l1 l2 lab lbc lac a b c = ()

val lemma3 : a:nat -> b:nat -> c:nat -> l:nat
           -> Lemma (ensures (a + (b + c - l) - l = (a + b - l) + c - l))
let lemma3 a b c l = ()

val merge_flag : l:history s o 
               -> a:history s o{fst (get_state a) >= fst (get_state l)}
               -> b:history s o{fst (get_state b) >= fst (get_state l)}
               -> bool
let merge_flag l a b =
  let lc = fst (get_state l) in
  let ac = fst (get_state a) in
  let bc = fst (get_state b) in
  let af = snd (get_state a) in
  let bf = snd (get_state b) in
  if af && bf then true
  else if not af && not bf then false
  else if af then ac - lc > 0
  else bc - lc > 0
  
val merge : a:history s o
          -> b:history s o
          -> l:history s o{wellformed l /\ is_lca l a b}
          -> s
let merge a b l = 
  History.lemma1 l;
  assert (wellformed a);

  let tra = get_trace l a in
  lemma1 tra (get_state l);
  assert (fst (get_state a) >= fst (get_state l));

  let trb = get_trace l b in
  lemma1 trb (get_state l);
  assert (fst (get_state b) >= fst (get_state l));

  let c = fst (get_state a) + fst (get_state b) - fst (get_state l) in
  let f = merge_flag l a b in
  c, f

val commutativity : a:history s o
                  -> b:history s o
                  -> l:history s o{wellformed l /\ is_lca l a b}
                  -> Lemma (ensures (merge a b l = merge b a l))
let commutativity a b l = ()

val idempotence : a:history s o{wellformed a /\ is_lca a a a}
                -> Lemma (ensures (merge a a a = get_state a))
let idempotence a = ()

val assoc1 : h:history s o{wellformed h}
           -> a:history s o{wellformed a /\ hbeq h a}
           -> b:history s o{wellformed b /\ hbeq h b}
           -> c:history s o{wellformed c /\ hbeq h c}
           -> l:history s o{lcau h a b = l /\ lcau h b c = l}
           -> mab:history s o{hbeq h mab /\ merge_node a b mab /\ get_state mab = merge a b l /\ lcau h mab c = l}
           -> mbc:history s o{hbeq h mbc /\ merge_node b c mbc /\ get_state mbc = merge b c l /\ lcau h a mbc = l}
           -> mabc1:history s o{hbeq h mabc1 /\ merge_node a mbc mabc1 /\ get_state mabc1 = merge a mbc l}
           -> mabc2:history s o{hbeq h mabc2 /\ merge_node mab c mabc2 /\ get_state mabc2 = merge mab c l}
           -> Lemma (get_state mabc1 = get_state mabc2)
let assoc1 h a b c l mab mbc mabc1 mabc2 =
  let cn h = fst (get_state h) in
  //let f h = snd (get_state h) in
  assert (cn mab = cn a + cn b - cn l);
  assert (cn mbc = cn b + cn c - cn l);
  
  let tra = get_trace l a in
  lemma1 tra (get_state l);
  let trb = get_trace l b in
  lemma1 trb (get_state l);
  let trc = get_trace l c in
  lemma1 trc (get_state l);
  //assert (f mab = merge_flag l a b);
  //assert (f mbc = merge_flag l b c);

  assert (cn mabc1 = cn a + cn mbc - cn l);
  assert (cn mabc1 = cn a + (cn b + cn c - cn l) - cn l);
  assert (cn mabc2 = cn mab + cn c - cn l);
  assert (cn mabc2 = (cn a + cn b - cn l) + cn c - cn l);
  lemma3 (cn a) (cn b) (cn c) (cn l);
  assert (cn mabc1 = cn mabc2);

  //assert (f mabc1 = merge_flag l a mbc);
  ()


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
                -> Lemma (True)//(get_state mabc1 = get_state mabc2)
let associativity h a b c lab lbc lac mab mbc m1 m2 mabc1 mabc2 = 
  lcau_associative h a b c lab lbc lac;
  let l = lcau h lab lac in
  let cn h = fst (get_state h) in
  //let f h = snd (get_state h) in
  let l2 = lcau h lab lac in
  let l1 = lcau h lbc lac in
  assert (l1 = l2);
  lemma2 (cn l1) (cn l2) (cn lab) (cn lbc) (cn lac) (cn a) (cn b) (cn c);
  assert (cn mabc1 = cn mabc2);

  let trab = get_trace l1 lab in
  lemma1 trab (get_state l1);
  let trbc = get_trace l1 lbc in
  lemma1 trbc (get_state l1);
  let trac = get_trace l1 lac in
  lemma1 trac (get_state l1);

  let tra = get_trace lab a in
  lemma1 tra (get_state lab);
  let tra' = append_trace (get_state l1) trab (get_state lab) tra (get_state a) in
  lemma1 tra' (get_state l);
  let tra = get_trace lac a in
  lemma1 tra (get_state lac);
  let tra' = append_trace (get_state l1) trac (get_state lac) tra (get_state a) in
  lemma1 tra' (get_state l);

  let trb = get_trace lab b in
  lemma1 trb (get_state lab);
  let trb' = append_trace (get_state l1) trab (get_state lab) trb (get_state b) in
  lemma1 trb' (get_state l);
  let trb = get_trace lbc b in
  lemma1 trb (get_state lbc);
  let trb' = append_trace (get_state l1) trbc (get_state lbc) trb (get_state b) in
  lemma1 trb' (get_state l);

  let trc = get_trace lac c in
  lemma1 trc (get_state lac);
  let trc' = append_trace (get_state l1) trac (get_state lac) trc (get_state c) in
  lemma1 trc' (get_state l)

(*
  let trc = get_trace lbc c in
  lemma1 trc (get_state lbc);
  let trc' = append_trace (get_state l1) trbc (get_state lbc) trc (get_state c) in
  lemma1 trc' (get_state l)
*)


instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity;
  History.idempotence = idempotence;
  History.associativity = associativity
}
