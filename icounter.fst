module Icounter

open FStar.List.Tot
open History

type o =
  | Inc : nat -> o

type s = nat

val apply_op : s -> o -> s
let apply_op s (Inc n) = s + n

instance _ : datatype s o = {
  History.apply_op = apply_op
}

val merge : {| datatype s o |}
          -> h:history s o{wellformed h}
          -> a:history s o{hbeq h a}
          -> b:history s o{hbeq h b}
          -> l:history s o{forall h'. mem h' (lca h a b) ==> h' = l}
          -> s
let merge h a b l = admit ()
  // get_state a + get_state b - get_state l

val commutativity : {| datatype s o |}
                  -> h:history s o{wellformed h}
                  -> a:history s o{hbeq h a}
                  -> b:history s o{hbeq h b}
                  -> l:history s o{forall h'. mem h' (lca h a b) ==> h' = l}
                  -> Lemma (ensures (merge h a b l = merge h b a l))
let commutativity h a b l = admit ()

instance _ : mrdt s o = {
  History.merge = merge;
  History.commutativity = commutativity
}
