module Rope

open FStar.List.Tot

#set-options "--query_stats"

type id = nat

type tree =
    | Leaf : (str:string) -> (sweight:nat{String.strlen str = sweight}) -> tree
    | Node : left:tree -> nweight:nat -> right:tree -> tree

val str_of_rope: a:tree -> Tot string
let rec str_of_rope a = match a with
  | Leaf s w -> s
  | Node l w r -> String.concat "" [(str_of_rope l);(str_of_rope r)]

val get_weight: a:tree -> Tot (w:nat{(exists (s:string{String.strlen s = w}). a = Leaf s w) \/ (exists l r. a = Node l w r)})
let get_weight a = match a with
  | Leaf _ w -> w
  | Node _ w _ -> w

val get_left: a:tree -> Tot (t:tree{(Leaf? a ==> t = a) /\ (Node? a ==> (exists w r. a = Node t w r))})
let get_left a = match a with
  | Node l _ _ -> l
  | _ -> a

val is_rope: a:tree -> Tot (b:bool {b = true <==> (get_weight a = String.length (str_of_rope (get_left a)))})
let is_rope a = get_weight a = String.length (str_of_rope (get_left a))

type rope = a:tree{is_rope a}

let _ = assert(is_rope (Node (Leaf (String.make 3 (Char.char_of_int 2)) 3) 3 (Leaf (String.make 1 (Char.char_of_int 3)) 1)))

[@@expect_failure]
let _ = assert(is_rope (Node (Leaf (String.make 3 (Char.char_of_int 2)) 3) 4 (Leaf (String.make 1 (Char.char_of_int 3)) 1)))

val index_r: r:rope -> i:nat{i < String.length (str_of_rope r)} -> Tot (c:String.char{String.index (str_of_rope r) i = c})


