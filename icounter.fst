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

val lemma2 : l1:nat -> l2:nat -> lab:nat  -> lbc:nat -> lac:nat  -> a:nat  -> b:nat -> c:nat 
             -> Lemma (requires l1 = l2)
                     (ensures (a + (b + c - lbc) - (lab + lac - l2)) = ((a + b - lab) + c - (lbc + lac - l1)))
let lemma2 l1 l2 lab lbc lac a b c = ()

val merge : a:history s o
          -> b:history s o
          -> l:history s o{wellformed l /\ is_lca l a b}
          -> history s o
let merge a b l = 
  History.lemma1 l;
  assert (wellformed a);

  let tr = get_trace l a in
  assert (fold_left apply_op (get_state l) tr = get_state a);

  lemma1 tr (get_state l);
  assert (get_state a >= get_state l);

  (HistLeaf 0 (get_state a + get_state b - get_state l))

assume val axiom1 : a:history s o
                  -> b:history s o
                  -> l:history s o{wellformed l /\ is_lca l a b}
                  -> Lemma (ensures hbeq l (merge a b l))

val sum : list (history s o) -> nat
let rec sum l =
  match l with
  |[] -> 0
  |x::xs -> (get_state x) + (sum xs)

val times : l:nat -> lca:history s o -> nat
let rec times l lca =
  match l with
  |0 -> 0
  |n -> (get_state lca) + (times (n - 1) lca)

val diff : lca:history s o 
         -> l:list (history s o)
         -> a:history s o{mem a l}
         -> l1:list (history s o) {(forall h'. mem h' l1 ==> mem h' l ) /\ 
                                  ((sum l1) - (times ((length l1)) lca) - (get_state lca) = 
                                  ((sum l) - (times (length l) lca) - (get_state a))) /\ (sum l1 = sum l - (get_state a))}
let rec diff lca l a =
  match l with
  |[] -> []
  |x::xs -> if (x = a) then xs else x::(diff lca xs a)

val mergeall : lca:history s o{wellformed lca} 
             -> a:history s o {hbeq lca a} 
             -> l:list (history s o){forall ele. mem ele l ==> hbeq lca ele /\ 
                                   (forall h' h''. hbeq lca h' /\ hbeq lca h'' ==> is_lca lca h' h'')}
             -> Tot (res:history s o {(get_state res) = (sum l) + (get_state a) - (times (length l) lca)}) (decreases l)
let rec mergeall lca a l =
  match l with
  |[] -> a
  |x::xs -> assert (wellformed lca); 
          assert (is_lca lca a x);
          axiom1 a x lca;
          mergeall lca (merge a x lca) xs

val lemma3 : lca:history s o {wellformed lca }
           -> l:list (history s o){(forall h'. mem h' l ==> hbeq lca h' /\ 
                                  (forall h' h''. hbeq lca h' /\ hbeq lca h'' ==> is_lca lca h' h''))}
           -> Lemma (ensures (forall a b. (mem a l /\ mem b l)  ==>
                            (get_state (mergeall lca a (diff lca l a)) = get_state (mergeall lca b (diff lca l b)))))
let lemma3 lca l = ()

val commutativity : a:history s o
                  -> b:history s o
                  -> l:history s o{wellformed l /\ is_lca l a b}
                  -> Lemma (ensures (get_state (merge a b l) = get_state (merge b a l)))
let commutativity a b l = ()

val idempotence : a:history s o{wellformed a /\ is_lca a a a}
                -> Lemma (ensures (get_state (merge a a a) = get_state a))
let idempotence a = ()

val associativity : h:history s o{wellformed h}
                -> a:history s o{wellformed a /\ hbeq h a}
                -> b:history s o{wellformed b /\ hbeq h b}
                -> c:history s o{wellformed c /\ hbeq h c}
                -> lab:history s o{lcau h a b = lab}
                -> lbc:history s o{lcau h b c = lbc}
                -> lac:history s o{lcau h c a = lac}
                -> mab:history s o{hbeq h mab /\ merge_node a b mab /\ get_state mab = get_state (merge a b lab)}
                -> mbc:history s o{hbeq h mbc /\ merge_node b c mbc /\ get_state mbc = get_state (merge b c lbc)}
                -> m1:history s o{hbeq h m1 /\ merge_node lab lac m1 /\ get_state m1 = get_state (merge lab lac (lcau h lab lac)) /\ lcau h a mbc = m1}
                -> m2:history s o{hbeq h m2 /\ merge_node lbc lac m2 /\ get_state m2 = get_state (merge lbc lac (lcau h lbc lac)) /\ lcau h mab c = m2}
                -> mabc1: history s o{hbeq h mabc1 /\ merge_node a mbc mabc1 /\ get_state mabc1 = get_state (merge a mbc m1)}
                -> mabc2: history s o{hbeq h mabc2 /\ merge_node mab c mabc2 /\ get_state mabc2 = get_state (merge mab c m2)}
                -> Lemma (get_state mabc1 = get_state mabc2)               
let associativity h a b c lab lbc lac mab mbc m1 m2 mabc1 mabc2 = 
  lcau_associative h a b c lab lbc lac;
  let l2 = lcau h lab lac in
  let l1 = lcau h lbc lac in
  lemma2 (get_state l1) (get_state l2) (get_state lab) (get_state lbc) (get_state lac) (get_state a) (get_state b) 
         (get_state c); ()

val convergence : h:history s o{wellformed h}
                -> lca:history s o{wellformed lca}
                -> l:list (history s o){(l = findleaf h) /\ (forall h'. mem h' l ==> hbeq lca h') /\ 
                                       (forall h' h''. hbeq lca h' /\ hbeq lca h'' ==> is_lca lca h' h'')}
                                       
                -> Lemma (ensures (forall a b. ((mem a l /\ mem b l)  ==>
                        (get_state (mergeall lca a (diff lca l a)) = 
                         get_state (mergeall lca b (diff lca l b))))))                                     
let convergence h lca l = 
  lemma3 lca l; 
  (*)assert (forall a. mem a l ==> is_lca a a a);*) ()
  
instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity;
  History.idempotence = idempotence;
  History.associativity = associativity
}
