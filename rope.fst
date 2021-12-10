module Rope

#set-options "--query_stats"

type id = nat

type tree =
    | Leaf : (str:string) -> (sweight:nat{String.strlen str = sweight}) -> tree
    | Node : left:tree -> nweight:nat -> right:tree -> tree

// Add some specs or Lemmas about this
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

val get_right: a:tree -> Tot (t:tree{(Leaf? a ==> t = a) /\ (Node? a ==> (exists l w. a = Node l w t))})
let get_right a = match a with
  | Node _ _ r -> r
  | _ -> a

val is_rope: a:tree -> Tot bool
let rec is_rope a = match a with
| Leaf s w -> w = String.length s
| Node l w r -> w = String.length (str_of_rope l) && is_rope l && is_rope r

type rope = a:tree{is_rope a}


val is_rope': a:rope -> Lemma (requires True) (ensures (get_weight a = String.length (str_of_rope (get_left a)) /\
                                                    (Node? a ==> is_rope (get_left a) /\ is_rope (get_right a)))) [SMTPat (is_rope a)]
let is_rope' a = ()

let _ = assert(is_rope (Node (Leaf (String.make 3 (Char.char_of_int 2)) 3) 3 (Leaf (String.make 1 (Char.char_of_int 3)) 1)))

[@@expect_failure]
let _ = assert(is_rope (Node (Leaf (String.make 3 (Char.char_of_int 2)) 3) 4 (Leaf (String.make 1 (Char.char_of_int 3)) 1)))

val get: r:rope -> i:nat{i < String.length (str_of_rope r)} -> Tot (c:String.char{String.index (str_of_rope r) i = c})

#set-options "--initial_fuel 5 --ifuel 5 --initial_ifuel 5 --fuel 5 --z3rlimit 10000"

let rec get tr i = match tr with
    | Leaf s w -> String.index s i
    | Node l w r -> assert(i < w ==> String.length (str_of_rope l) >= i);
                   assert(i >= w ==> String.length (str_of_rope l) <= i);
                   assert(i < w ==> (exists c. String.index (str_of_rope l) i = c));
                   // assert(i >= w ==> (exists c. String.index (str_of_rope r) (i-w) = c));
                   if i < w then (admit(); get l i) else (admit(); get r (i-w))

val set: r:rope -> c:String.char -> i:nat{i < String.length (str_of_rope r)} ->
                Tot (res:rope{String.length (str_of_rope r) = String.length (str_of_rope res) /\
                                            (forall (x:nat{x < String.length (str_of_rope r)}). (get r x = get res x) \/ (x = i /\ get res x = c))})

val split: r:rope -> i:nat{i < String.length (str_of_rope r)} ->
                  Tot (res:(rope * rope){str_of_rope r =  String.concat "" [(str_of_rope (fst res));(str_of_rope (snd res))]})

let split r i = admit(); (r, r)

val concat: r1:rope -> r2:rope -> Tot (r:rope{str_of_rope r = String.concat "" [(str_of_rope r1);(str_of_rope r2)]})

val insert: r:rope -> i:nat{i < String.length (str_of_rope r)} -> s:string ->
                   Tot (res:rope{str_of_rope res = String.concat "" [str_of_rope (fst (split r i)) ; s ; str_of_rope (snd (split r i))]})


val delete: r:rope -> i:nat{i < String.length (str_of_rope r)} -> j:nat{i < j /\ j < String.length (str_of_rope r)}
            -> Tot (res:rope{str_of_rope res = String.concat "" [str_of_rope (fst (split r i)); str_of_rope (snd (split r j))]})



