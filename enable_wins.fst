module Enable_wins

open FStar.Tactics
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
  else if af then ac > lc
  else bc > lc
  
val merge : a:history s o
          -> b:history s o
          -> l:history s o{wellformed l /\ is_lca l a b}
          -> r:s{fst r >= fst (get_state a) /\ 
                fst r >= fst (get_state b) /\ 
                fst r >= fst (get_state l)}
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
  
  //let tra = get_trace l a in
  //lemma1 tra (get_state l);
  //let trb = get_trace l b in
  //lemma1 trb (get_state l);
  //let trc = get_trace l c in
  //lemma1 trc (get_state l);
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

let tau () =
  Tactics.simpl ();
  dump "Todo"

[@"substitute"]
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
  let f h = snd (get_state h) in
  let l2 = lcau h lab lac in
  let l1 = lcau h lbc lac in
  assert (l1 = l2);
  lemma2 (cn l1) (cn l2) (cn lab) (cn lbc) (cn lac) (cn a) (cn b) (cn c);
  assert (cn mabc1 = cn mabc2);
  
  //assert (f mabc1 = merge_flag m1 a mbc);
  //assert (cn a >= cn m1);
  //assert (cn mbc >= cn m1);
  assert (f mabc1 = 
          begin if f a && f mbc then true
                else if not (f a) && not (f mbc) then false
                else if f a then cn a > cn m1
                else cn mbc > cn m1
          end);
  assert (f mabc2 = 
          begin if f mab && f c then true
                else if not (f mab) && not (f c) then false
                else if f mab then cn mab > cn m2
                else cn c > cn m2
          end);
  let f_mab = 
    if f a && f b then true 
    else if not (f a) && not (f b) then false
    else if f a then cn a > cn lab
    else cn b > cn lab
  in
  assert (f mab = f_mab);
  assert_norm (f mabc2 = 
          begin if f_mab && f c then true
                else if not (f_mab) && not (f c) then false
                else if f_mab then cn mab > cn m2
                else cn c > cn m2
          end);

  (*
  let f_mbc = 
    if f b && f c then true 
    else if not (f b) && not (f c) then false
    else if f b then cn b > cn lbc
    else cn c > cn lbc
  in
  assert (f mbc = f_mbc);

  assert (f mabc1 = 
          begin if f a && f_mbc then true
                else if not (f a) && not (f_mbc) then false
                else if f a then cn a > cn m1
                else cn mbc > cn m1
          end);
  *)

  //assert_by_tactic (f mabc1 = f mabc2) tau;
   
  ()
  
instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity;
  History.idempotence = idempotence;
  History.associativity = associativity
}
