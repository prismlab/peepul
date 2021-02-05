module Gset

open FStar.List.Tot
open History

type o =
  | Add : nat -> o

type s = list nat

val app_op : s -> o -> s
let app_op s (Add n) = n::s

instance icounter : datatype s o = {
  History.apply_op = app_op
}

val union : l1:s -> l2:s -> l3:s -> Tot(l:s {(forall ele. mem ele l <==> mem ele l1 \/ mem ele l2 \/ mem ele l3)} )
let rec union l1 l2 l3 =
  match l1,l2,l3 with
  |[],[],[] -> []
  |x::xs,_,_ -> if (mem x xs || mem x l2 || mem x l3) then (union xs l2 l3) else x::(union xs l2 l3)
  |[],y::ys,_ -> if(mem y ys || mem y l3) then (union l1 ys l3) else y::(union l1 ys l3)
  |[],[],z::zs -> if (mem z zs) then (union l1 l2 zs) else z::(union l1 l2 zs)
  
val merge : a:history s o
          -> b:history s o
          -> l:history s o{wellformed l /\ is_lca l a b  }
          -> s
let merge a b l = 
  union (get_state a) (get_state b) (get_state l) 

(*Axiom for equality of lists*)
assume val equal : l1:s -> l2:s -> Lemma (ensures ((forall ele. mem ele l1 <==> mem ele l2) ==> l1 = l2))

val commutativity : a:history s o
                  -> b:history s o
                  -> l:history s o{wellformed l /\ is_lca l a b}
                  -> Lemma (ensures (merge a b l = merge b a l))
let  commutativity a b l = 
  equal (merge a b l) (merge b a l); ()
 

val idempotence : a:history s o{wellformed a /\ is_lca a a a}
                -> Lemma (ensures ((merge a a a) = (get_state a)))
let idempotence a = 
  equal (merge a a a) (get_state a); ()

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
  equal (get_state mabc1) (get_state mabc2); ()
  
instance _ : mrdt s o icounter = {
  History.merge = merge;
  History.commutativity = commutativity;
  History.idempotence = idempotence;
  History.associativity = associativity
}
