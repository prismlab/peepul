module Orset_bst1

open FStar.List.Tot
module O = Orset_opt


(*)let l = [3;2;1]


let l' = sortWith (fun a b -> a - b) l

let _ = assert (l' = [1;2;3])*)

type tree =
    |Leaf : tree
    |Node : (nat (*unique id*) * nat (*unique element*)) -> tree -> tree -> tree

#set-options "--query_stats"

val memt1 : (nat * nat) 
            -> tree 
            -> Tot bool
let rec memt1 x t =
    match t with
    | Leaf -> false
    | Node n t1 t2 -> x = n || memt1 x t1 || memt1 x t2

val member_id : id:nat
              -> t:tree
              -> Tot (b:bool {(exists ele. memt1 (id,ele) t) <==> b = true})
let rec member_id id t =
    match t with
    | Leaf -> false
    | Node (id1,_) t1 t2 -> id = id1 || member_id id t1 || member_id id t2

val member_ele : ele:nat 
               -> t:tree 
               -> Tot (b:bool {(exists id. memt1 (id,ele) t) <==> b = true})
let rec member_ele ele t =
  match t with
  | Leaf -> false
  | Node (_,ele1) t1 t2 -> ele = ele1 || member_ele ele t1 || member_ele ele t2

val forallt : p:((nat * nat) -> Tot bool)
            -> t:tree 
            -> Tot (r:bool{r = true <==> (forall x. memt1 x t ==> p x)})
let rec forallt p t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> p n && forallt p t1 && forallt p t2

val unique_id : t:tree -> Tot bool
let rec unique_id t =
  match t with
  |Leaf -> true
  |Node (id,ele) t1 t2 -> not (member_id id t1) && not (member_id id t2) &&
                         forallt (fun e -> not (member_id (fst e) t2)) t1 && 
                         forallt (fun e -> not (member_id (fst e) t1)) t2 &&
                         unique_id t1 && unique_id t2 

val unique_ele : t:tree -> Tot bool
let rec unique_ele t =
  match t with
  |Leaf -> true
  |Node (id,ele) t1 t2 -> not (member_ele ele t1) && not (member_ele ele t2) &&
                           forallt (fun e -> not (member_ele (snd e) t2)) t1 && 
                           forallt (fun e -> not (member_ele (snd e) t1)) t2 &&
                           unique_ele t1 && unique_ele t2

val is_bst : tree -> Tot bool
let rec is_bst t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> forallt (fun n' -> snd n > snd n') t1 &&
                   forallt (fun n' -> snd n < snd n') t2 && is_bst t1 && is_bst t2

val size : t1:tree -> Tot nat
let rec size t1 =
  match t1 with
  |Leaf -> 0
  |Node _ t1 t2 -> 1 + size t1 + size t2

type t = tree1:tree {is_bst tree1 /\ unique_id tree1}

val help : t1:t -> Lemma (ensures unique_ele t1)
                  [SMTPat (is_bst t1)]
#set-options "--z3rlimit 1000000"
let rec help tr = 
  match tr with
  |Leaf -> ()
  |Node n t1 t2 -> help t1 ; help t2

val memt : ele:(nat * nat)
         -> t1:t
         -> Tot (b:bool {(memt1 ele t1 <==> b = true)})
let rec memt x t =
  match t with
  |Leaf -> false
  |Node n t1 t2 -> if x = n then true
                     else if (snd x < snd n) then memt x t1
                         else memt x t2

val ge : (nat * nat) -> (nat * nat) -> Tot bool
let ge n1 n2 = (snd n1 > snd n2 && fst n1 <> fst n2) || n1 = n2

val find_max : t1:tree {Node? t1}
             -> Pure (nat * nat)
               (requires (is_bst t1 /\ unique_id t1))
               (ensures (fun r -> (forallt (ge r) t1) /\ memt1 r t1))
let rec find_max t1 =
  match t1 with
  | Node v _ t2 -> 
    match t2 with
    | Leaf -> v
    | _ -> find_max t2

val delete_ele : x:nat
               -> t1:t
               -> Pure t
                 (requires true)
                 (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1) /\ snd e <> x) /\ not (member_ele x r) /\ 
                                   is_bst r /\ unique_id r)) 
                 (decreases (size t1))

#set-options "--z3rlimit 1000000"
let rec delete_ele x tr = 
  match tr with
  | Leaf -> Leaf
  | Node n t1 t2 -> if snd n = x then
                      match t1, t2 with
                      | Leaf, Leaf -> Leaf
                      | _   , Leaf -> t1
                      | Leaf, _    -> t2
                      | _           -> assert (Node? t1); let y = find_max t1 in Node y (delete_ele (snd y) t1) t2
                   else if x < snd n then Node n (delete_ele x t1) t2
                        else Node n t1 (delete_ele x t2)
(*104556 ms*)

val delete : x:(nat * nat)
           -> t1:t
           -> Pure t
             (requires (memt x t1))
             (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1) /\ e <> x) /\ not (memt x r) /\ is_bst r 
                                   /\ unique_id r)) 
             (decreases (size t1))

#set-options "--z3rlimit 1000000"
let rec delete x tr = 
  match tr with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then
                      match t1, t2 with
                      | Leaf, Leaf -> Leaf
                      | _   , Leaf -> t1
                      | Leaf, _    -> t2
                      | _           -> assert (Node? t1); let y = find_max t1 in Node y (delete y t1) t2
                   else if snd x < snd n then Node n (delete x t1) t2
                     else Node n t1 (delete x t2)
(*62485 ms*)

#set-options "--z3rlimit 1000000"
val update : ele:nat
           -> id:nat
           -> t1:t
           -> Pure tree
             (requires not (member_id id t1))
             (ensures (fun res -> (forall e. memt e t1 /\ snd e <> ele <==> memt1 e res /\ snd e <> ele) /\
                               (forall e. memt1 e res /\ fst e <> id /\ member_id (fst e) res <==> 
                                     memt e t1 /\ snd e <> ele /\ member_id (fst e) t1) /\
                               (forall e. member_ele e t1 \/ e = ele <==> member_ele e res) /\
                               (forall e. memt1 e res /\ e <> (id,ele) <==> memt e t1 /\ snd e <> ele) /\ 
                                     memt1 (id,ele) res /\ is_bst res /\ unique_id res))

#set-options "--z3rlimit 1000000"
let rec update ele id tr =
  match tr with
  |Leaf -> Node (id,ele) Leaf Leaf
  |Node (id1,ele1) t1 t2 -> if ele = ele1 then Node (id, ele1) t1 t2
                              else if ele < ele1 then (Node (id1,ele1) (update ele id t1) t2)
                                 else Node (id1,ele1) t1 (update ele id t2)
(*1177895 ms*)

val app_op : s1:t
           -> op:O.o
           -> Pure t
             (requires (not (member_id (O.get_id op) s1)))
             (ensures (fun res -> (O.opa op ==> (forall e. memt e s1 /\ snd e <> O.get_ele op <==> 
                                              memt e res /\ snd e <> O.get_ele op) /\
                               (forall e. memt e res /\ fst e <> O.get_id op /\ member_id (fst e) res <==> 
                                     memt e s1 /\ snd e <> O.get_ele op /\ member_id (fst e) s1) /\
                               (forall e. member_ele e s1 \/ e = O.get_ele op <==> member_ele e res) /\
                               (forall e. memt e res /\ e <> ((O.get_id op), (O.get_ele op)) <==> 
                                     memt e s1 /\ snd e <> O.get_ele op) /\
                                     memt ((O.get_id op), (O.get_ele op)) res) /\
                               (O.opr op ==> (forall e. memt e res <==> memt e s1 /\ snd e <> O.get_ele op))))

let app_op s1 op =
  if O.opa op then update (O.get_ele op) (O.get_id op) s1 else delete_ele (O.get_ele op) s1

val insert : x:(nat * nat)
           -> t1:t
           -> Pure tree
             (requires (not (memt x t1) /\ not (member_id (fst x) t1) /\ not (member_ele (snd x) t1)))
             (ensures (fun r -> is_bst r /\ (forall y. memt1 y r <==> (memt y t1 \/ x = y)) /\ unique_id r))
             (decreases (size t1))

#set-options "--z3rlimit 1000000"
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then t
                      else if snd x < snd n then (let y = insert x t1 in Node n (insert x t1) t2)
                        else Node n t1 (insert x t2)
(*47764 ms*)

val totree1 : s1:O.s
            -> acc:t
            -> Pure t
              (requires (forall e. member_id e acc ==> not (O.member_id e s1)) /\
                        (forall e. member_ele e acc ==> not (O.member_ele e s1)))
              (ensures (fun t1 -> (forall e. memt e t1 <==> mem e s1 \/ memt e acc)))

#set-options "--initial_fuel 10000000 --initial_ifuel 10000000"
#set-options "--z3rlimit 1000000"
let rec totree1 l acc =
    match l with
    |[] -> acc
    |x::xs -> totree1 xs (insert x acc)

val totree : l:O.s -> t1:t {(forall e. memt e t1 <==> mem e l) /\
                           (forall e. member_ele e t1 <==> O.member_ele e l) /\
                           (forall e. member_id e t1 <==> O.member_id e l)}
let totree l = totree1 l Leaf

val lt : n1:(nat * nat) 
       -> n2:(nat * nat)
       -> Tot (b:bool)
let lt (id,ele) (id1,ele1) = (ele < ele1 && id <> id1)

val appendt : l1:O.s
            -> l2:O.s
            -> Pure O.s
              (requires (forall e. O.member_ele e l1 ==> not (O.member_ele ( e) l2)) /\
                        (forall e. O.member_id e l1 ==> not (O.member_id ( e) l2)))
              (ensures (fun res -> (forall e. mem e res <==> mem e l1 \/ mem e l2) /\
                                (forall e. O.member_id e res <==> O.member_id e l1 \/ O.member_id e l2) /\
                                (forall e. O.member_ele e res <==> O.member_ele e l1 \/ O.member_ele e l2)))
let rec appendt l1 l2 =
    match l1,l2 with
    |[],[] -> []
    |x::xs,_ -> x::(appendt xs l2)
    |[],_ -> l2

val flatten : tree1:t
            -> Pure O.s
              (requires true)
              (ensures (fun res -> (forall e. memt e tree1 <==> mem e res) /\
                                (forall e. member_ele e tree1 <==> O.member_ele e res) /\
                                (forall e. member_id e tree1 <==> O.member_id e res)))
              (decreases (size tree1))

#set-options "--z3rlimit 1000000"
let rec flatten t =
    match t with
    |Leaf -> []
    |Node n t1 t2 -> assert ((forall e. O.member_ele e (flatten t1) ==> not (O.member_ele ( e) (flatten t2))) /\
                            (forall e. O.member_id e (flatten t1) ==> not (O.member_id ( e) (flatten t2))) /\
                            not (O.member_id (fst n) ( (flatten t1) )) /\
                            not (O.member_ele (snd n) ( (flatten t1) )) /\
                            not (O.member_id (fst n) ( (flatten t2) )) /\
                            not (O.member_ele (snd n) ( (flatten t2) )));
                     assert (not (O.member_id (fst n) (appendt (flatten t1) (flatten t2))) /\
                             not (O.member_ele (snd n) (appendt (flatten t1) (flatten t2))));
                     n::(appendt (flatten t1) (flatten t2))

val fst : (nat * nat) -> nat
let fst (id,ele) = id
val snd : (nat * nat) -> nat
let snd (id,ele) = ele

#set-options "--query_stats"
val sim : tr:O.ae
        -> s1:t
        -> Tot (b:bool {(b = true <==> (forall e. memt e s1 ==> (forall a. mem a tr.l /\ O.opa a /\ snd e = O.get_ele a ==>
                                      (forall r. mem r tr.l /\ O.opr r /\ O.get_ele a = O.get_ele r ==> 
                                      not (O.get_id a <> O.get_id r && tr.vis a r)) ==> fst e >= O.get_id a) /\ 
                 (mem ((fst e), O.Add (snd e)) tr.l /\
                 (forall r. mem r tr.l /\ O.opr r /\ O.get_ele r = snd e ==> not (fst e <> O.get_id r && tr.vis ((fst e), O.Add (snd e)) r)))) /\
                 (forall a. mem a tr.l /\ O.opa a ==> (forall r. mem r tr.l /\ O.opr r /\ O.get_ele a = O.get_ele r && O.get_id a <> O.get_id r ==> not (tr.vis a r)) ==> member_ele (O.get_ele a) s1))})

#set-options "--z3rlimit 1000000"
let sim tr s1 = 
    let lsta = (O.filter (fun a -> O.opa a) tr.l) in
    let lstr = (O.filter (fun r -> O.opr r) tr.l) in
    let lst = O.filter (fun a -> not (O.existsb (fun r -> O.get_id a <> O.get_id r && 
              O.get_ele r = O.get_ele a && tr.vis a r) lstr)) lsta in

    (forallt (fun e -> (O.forallb (fun a -> fst e >= O.get_id a) (O.filter (fun a -> O.get_ele a = snd e) lst)) &&
                    (mem ((fst e), O.Add (snd e)) tr.l &&
                    not (O.existsb (fun r -> fst e <> O.get_id r && tr.vis ((fst e), O.Add (snd e)) r ) 
                    (O.filter (fun r -> snd e = O.get_ele r) lstr)))) s1) &&
    (O.forallb (fun a -> member_ele (O.get_ele a) s1) lst)
(*541617 ms*)

val diff : a:t
         -> l:t
         -> Pure t
           (requires true)
           (ensures (fun d -> (forall e. memt e d <==> memt e a /\ not (memt e l)) /\
                           (forall e. memt e d /\ member_id (fst e) d <==> 
                                 memt e a /\ member_id (fst e) a /\ not (memt e l)) /\
                           (forall e. memt e d  /\ member_ele (snd e) d <==> 
                                 memt e a /\ member_ele (snd e) a /\ not (memt e l)) /\
                           (forall e. memt e a /\ memt e l ==> not (member_ele (snd e) d) /\
                                                         not (member_id (fst e) d))))
          (decreases %[l;a])
let diff a l =
  totree (O.diff (flatten a) (flatten l))

(*)val lem_sort : l:list (nat * nat)
             -> Lemma (requires (O.unique_id l /\ O.unique_ele l))
                               (ensures (O.unique_id (sortWith (fun x y -> snd y - snd x) l)) /\
                                 (O.unique_ele (sortWith (fun x y -> snd y - snd x) l)) /\
                                 (sorted (sortWith (fun x y -> snd y - snd x) l)))
               (decreases l)

#set-options "--z3rlimit 10000000"
let rec lem_sort l =
  match l with
  |[] -> ()
  |x::[] -> ()
  |x::y::xs -> lem_sort (y::xs)*)

let l = [(3,3); (2,2)]

val check : l:list (nat * nat) -> Tot (l1:list (nat * nat))
let check l = sortWith (fun a b -> snd b - snd a) l

let l' = check [(3,3); (1,1); (2,2)]


let max n1 n2 = if n1 > n2 then n1 else n2

val pos : l:O.s
        -> ele:(nat * nat)
        -> Pure nat
          (requires (mem ele l))
          (ensures (fun p -> true))
let rec pos l e =
  match l with
  |x::y -> if x = e then 0 else 1 + pos y e

val sorted : l:O.s
           -> Tot bool
             (decreases (length l))
let rec sorted l =
  match l with
  |[] -> true
  |x::[] -> true
  |x::y::xs -> snd x < snd y && sorted (y::xs)

val take_element : l:O.s
                 -> pos1:nat
                 -> Pure O.s
                   (requires (pos1 < length l) /\ length l >= 1 /\ sorted l)
                   (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e = pos1) /\ length r = 1 /\ sorted r /\
                                   (forall e. mem e r /\ O.member_id (fst e) r <==>
                                   mem e l /\ O.member_id (fst e) l /\ pos l e = pos1)))
                   (decreases %[(length l); pos1])
#set-options "--z3rlimit 10000000"
let rec take_element l n =
  match l with
  | h::t -> if n > 0 then take_element t (n-1) else [h]

val takemiddle : l:O.s
               -> Pure O.s
                 (requires (sorted l /\ length l >= 1))
                 (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e = length l/2) /\
                                 (forall e. mem e r /\ O.member_id (fst e) r <==> mem e l /\ 
                                 O.member_id (fst e) l /\ pos l e = length l/2)/\ length r = 1))
let takemiddle l = take_element l (length l/2)

val take : pos1:nat
         -> l:O.s
         -> Pure O.s
           (requires (pos1 < length l /\ sorted l))
           (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e < pos1) /\
                           (forall e. mem e r /\ O.member_id (fst e) r <==> 
                                 mem e l /\ O.member_id (fst e) l /\ pos l e < pos1) 
                            /\ O.unique_id r /\ length r = pos1 /\
                           (forall e. mem e r ==> pos l e < pos1))) 
           (decreases %[pos1;l])
#set-options "--z3rlimit 10000000"
let rec take n l =
  if n = 0 then []
    else (match l with |h::t -> h:: take (n-1) t)

val takesorted : pos1:nat
               -> l:O.s
               -> Lemma (requires (pos1 < length l) /\ (sorted l))
                       (ensures (sorted (take pos1 l)))
                       (decreases %[pos1;(length l)])
#set-options "--z3rlimit 10000000"
let rec takesorted n l = 
  if n = 0 then () else
    match l with
    |[] -> ()
    |x::y -> takesorted (n - 1) y

val takefront : l:O.s
              -> Pure O.s
                (requires (sorted l /\ length l >= 1))
                (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e < (length l/2)) /\
                                (forall e. mem e r /\ O.member_id (fst e) r <==> 
                                      mem e l /\ O.member_id (fst e) l /\ pos l e < (length l/2)) 
                                      /\ sorted r /\ length r = (length l)/2))
                (decreases l)
#set-options "--z3rlimit 10000000"
let takefront l = 
  let t = take (length l/2) l in
  takesorted (length l/2) l;
  t

val drop : pos1:nat
         -> l:O.s
         -> Pure O.s
           (requires (pos1 <= length l /\ sorted l))
             (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e >= pos1) /\
                             (forall e. mem e r /\ O.member_id (fst e) r <==> 
                                   mem e l /\ O.member_id (fst e) l /\ pos l e >= pos1)
                                   /\ sorted r /\ length r = length l - pos1))
           (decreases %[pos1;l])
let rec drop n l =
  if n = 0 then l else
    (match l with
     | h::t -> drop (n-1) t)

val takeback : l:O.s
             -> Pure O.s
               (requires (sorted l /\ length l >= 1))
               (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e > (length l/2)) /\
                               (forall e. mem e r /\ O.member_id (fst e) r <==> 
                                     mem e l /\ O.member_id (fst e) l /\ pos l e > (length l/2)) 
                                     /\ sorted r /\ length r = ((length l) - (length l)/2 - 1)))
               (decreases l)
let takeback l = drop (length l/2 + 1) l

val tree_of_list : l:O.s
                 -> Pure tree
                   (requires (sorted l))
                   (ensures (fun r -> (size r = length l) /\
                            (forall e. memt1 e r <==> mem e l) /\
                            (forall id. member_id id r <==> O.member_id id l) /\
                            (forall ele. member_ele ele r <==> O.member_ele ele l)))
                   (decreases %[length l])

#set-options "--z3rlimit 1000000"
let rec tree_of_list l  =
  match l with
  | [] -> Leaf
  | h::[] -> Node h Leaf Leaf
  | h::t -> Node (hd (takemiddle l)) (tree_of_list (takefront l)) (tree_of_list (takeback l) )

val lem_tree : l:O.s
             -> Lemma (requires sorted l)
                     (ensures (is_bst (tree_of_list l) /\ unique_id (tree_of_list l)))
let lem_tree l = admit ()

val lem_sort : l:list (nat * nat)
             -> Lemma (requires (O.unique_id l /\ O.unique_ele l))
                     (ensures (O.unique_id (sortWith (fun x y -> snd y - snd x) l)) /\
                              (O.unique_ele (sortWith (fun x y -> snd y - snd x) l)) /\
                              (sorted (sortWith (fun x y -> snd y - snd x) l)) /\
                                (forall e. mem e l <==> mem e (sortWith (fun x y -> snd y - snd x) l)) /\
                                  (forall id. O.member_id id l <==> O.member_id id (sortWith (fun x y -> snd y - snd x) l)) /\
                                    (forall ele. O.member_ele ele l <==> O.member_ele ele (sortWith (fun x y -> snd y - snd x) l)))
                  (decreases l)

#set-options "--z3rlimit 10000000"
let rec lem_sort l =
    match l with
    |[] -> ()
    |x::[] -> ()
    |x::y::xs -> admit (); lem_sort (y::xs)

let l = [(2,2);(1,1);(3,3);(10,10);(5,5)]
let l' = sortWith (fun x y -> snd y - snd x) l
let _ = assert (l' = [(1,1);(2,2);(3,3);(5,5);(10,10)] /\ sorted l')

val merge : ltr:O.ae
          -> l:t
          -> atr:O.ae
          -> a:t
          -> btr:O.ae
          -> b:t
          -> Pure t (requires (forall e. mem e ltr.l ==> not (O.member (O.get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (O.member (O.get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (O.member (O.get_id e) btr.l)) /\
                             (sim ltr l /\ sim (O.union ltr atr) a /\ sim (O.union ltr btr) b) /\ 
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> O.get_id e < O.get_id e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> O.get_id e < O.get_id e1) /\
                             (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))))
                (ensures (fun res -> true))

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b = 
    let m = O.merge ltr (flatten l) atr (flatten a) btr (flatten b) in
    assert (O.unique_id m /\ O.unique_ele m); 
    let m' = sortWith (fun x y -> snd y - snd x) m in
    lem_sort m;
    assert (sorted m');
    lem_tree m';
    tree_of_list m'
(*90020 ms*)

#set-options "--z3rlimit 10000000"
val prop_merge : ltr:O.ae
               -> l:t
               -> atr:O.ae
               -> a:t
               -> btr:O.ae
               -> b:t
               -> Lemma (requires (forall e. mem e ltr.l ==> not (O.member (O.get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (O.member (O.get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (O.member (O.get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (O.union ltr atr) a /\ sim (O.union ltr btr) b) /\ 
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> O.get_id e < O.get_id e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> O.get_id e < O.get_id e1) /\
                                 (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))))
                       (ensures (sim (O.absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  O.prop_merge ltr (flatten l) atr (flatten a) btr (flatten b);
  ()
(*122427 ms*)

val prop_oper : tr:O.ae
              -> st:t
              -> op:O.o 
              -> Lemma (requires (sim tr st) /\ 
                                (not (O.member (O.get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> O.get_id e < O.get_id op))
                      (ensures (sim (O.append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op =
  assert (not (member_id (O.get_id op) st)); 
  O.prop_oper tr (flatten st) op;
  ()
 (*240793 ms*)

val convergence : tr:O.ae
                -> a:t
                -> b:t  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. memt e a <==> memt e b))
let convergence tr a b = 
  O.convergence tr (flatten a) (flatten b);
  ()






(*
type color =
  | Red
  | Black

  val chain : option (nat * nat) -> (nat * nat) -> option (nat * nat) -> bool
  let chain x y z =
    match x, z with
    | Some x, Some z -> snd x <= snd y && snd y <= snd z
    | Some x, None -> snd x <= snd y
    | None, Some z -> snd y <= snd z
    | _ -> true

  type rbnode : h:nat -> c:color -> Type =
  | Leaf :
    rbnode 1 Black
  | R : #h:nat ->
    left:rbnode h Black -> value:(nat * nat) -> right:rbnode h Black ->
    rbnode h Red
  | B : #h:nat -> #cl:color -> #cr:color ->
    left:rbnode h cl -> value:(nat * nat) -> right:rbnode h cr ->
    rbnode (h+1) Black

val reduceNode : #h:nat -> #c:color
    -> f:((nat * nat) -> (nat * nat) -> (nat * nat)) -> root:rbnode h c -> Tot (option (nat * nat)) (decreases root)
  let rec reduceNode #h #c f = function
    | Leaf -> None
    | B left value right
    | R left value right ->
      match reduceNode f left, reduceNode f right with
      | Some l, Some r -> Some (f value (f l r))
      | Some x, None
      | None, Some x -> Some (f x value)
      | None, None -> Some value

val min: #h:nat -> #c:color -> t:rbnode h c -> option (nat * nat)
let min #h #c t = reduceNode (fun x y -> if snd x < snd y then x else y) t

val max: #h:nat -> #c:color -> t:rbnode h c -> option (nat * nat)
let max #h #c t = reduceNode (fun x y -> if snd x > snd y then x else y) t

val sorted : #h:nat -> #c:color -> root:rbnode h c -> Tot bool (decreases root)
let rec sorted #h #c = function
    | Leaf -> true
    | B left value right
    | R left value right ->
      sorted left && sorted right && chain (max left) value (min right)

type tree =
    | RBTree : #h:nat -> root:rbnode h Black {sorted root} -> tree

    type hiddenTree : h:nat -> Type =
    | HR : #h:nat -> node:rbnode h Red -> hiddenTree h
    | HB : #h:nat -> node:rbnode (h+1) Black -> hiddenTree (h+1)


    type almostNode : h:nat -> Type =
    | LR : #h:nat -> #cR:color -> left:rbnode h Red -> value:(nat * nat) -> right:rbnode h cR -> almostNode h
    | RR : #h:nat -> #cL:color -> left:rbnode h cL -> value:(nat * nat) -> right:rbnode h Red -> almostNode h
    | V : #h:nat -> #c:color -> node:rbnode h c -> almostNode h

    val balanceLB : #h:nat -> #c:color -> almostNode h -> (nat * nat) -> rbnode h c -> Tot (hiddenTree (h+1))
    let balanceLB #h #c left z d =
    match left with
    | LR (R a x b) y c
    | RR a x (R b y c) -> HR (R (B a x b) y (B c z d))
    | V axb -> HB (B axb z d)

    val balanceRB : #h:nat -> #c:color -> rbnode h c -> (nat * nat) -> almostNode h -> Tot (hiddenTree (h+1))
    let balanceRB #h #c a x right =
    match right with
    | LR (R b y c) z d
    | RR b y (R c z d) -> HR (R (B a x b) y (B c z d))
    | V cyd -> HB (B a x cyd)

    val balanceLR : #h:nat -> #c:color -> hiddenTree h -> (nat * nat) -> rbnode h c -> Tot (almostNode h)
    let balanceLR #h #c left x right =
    match left with
    | HR a -> LR a x right
    | HB a ->
      match right with
      | R b y c -> RR a x (R b y c)
      | B b y c -> V (R a x (B b y c))
      | Leaf -> V (R a x Leaf)

    val balanceRR : #h:nat -> #c:color -> rbnode h c -> (nat * nat) -> hiddenTree h -> Tot (almostNode h)
    let balanceRR #h #c left y right =
    match right with
    | HR c -> RR left y c
    | HB c ->
      match left with
      | R a x b -> LR (R a x b) y c
      | B a x b -> V (R (B a x b) y c)
      | Leaf -> V (R Leaf y c)

    val ins : #h:nat -> #c:color -> x:(nat * nat) -> s:rbnode h c -> Tot (almostNode h) (decreases s)
    val insB : #h:nat -> x:(nat * nat) -> s:rbnode h Black -> Tot (hiddenTree h) (decreases s)
    let rec ins #h #c x = function
    | Leaf -> V (R Leaf x Leaf)
    | B a y b ->
      (if snd x < snd y then
      match balanceLB (ins x a) y b with
      | HR r -> V r
      | HB b -> V b
      else if x = y then V (B a y b)
      else match balanceRB a y (ins x b) with
      | HR r -> V r
      | HB b -> V b)
    | R a y b ->
      (if snd x < snd y then balanceLR (insB x a) y b
      else if x = y then V (R a y b)
      else balanceRR a y (insB x b))
    and insB #h x = function
    | Leaf -> HR (R Leaf x Leaf )
    | B a y b ->
      if snd x < snd y then balanceLB (ins x a) y b
      else if x = y then HB (B a y b)
      else balanceRB a y (ins x b)

    val mem : #h:nat -> #c:color -> x:(nat * nat) -> s:rbnode h c -> Tot bool (decreases s)
    let rec mem #h #c x = function
    | Leaf -> false
    | B l y r
    | R l y r -> x = y || mem x l || mem x r

    val hiddenTree_mem : #h:nat -> (nat * nat) -> hiddenTree h -> bool
    let hiddenTree_mem #h x = function
    | HB root
    | HR root -> mem x root

    val almostNode_mem : #h:nat -> (nat * nat) -> almostNode h -> bool
    let almostNode_mem #h x = function
    | LR a y b
    | RR a y b -> mem x (B a y b)
    | V root -> mem x root


    val ins_mem : #h:nat -> #c:color -> x:(nat * nat) -> s:rbnode h c ->
    Lemma (ensures forall y. (mem y s \/ y = x) <==> almostNode_mem y (ins x s)) (decreases s)

    val insB_mem : #h:nat -> x:(nat * nat) -> s:rbnode h Black ->
    Lemma (ensures forall y. (mem y s \/ y = x) <==> hiddenTree_mem y (insB x s)) (decreases s)



    #push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 4"
    let rec ins_mem #h #c x = function
    | Leaf -> ()
    | B a y b ->
      if snd x < snd y then ins_mem x a
      else if x = y then ()
      else ins_mem x b
    | R a y b ->
      if snd x < snd y then insB_mem x a
      else if x = y then ()
      else insB_mem x b
    and insB_mem #h x = function
    | Leaf -> ()
    | B a y b ->
      if snd x < snd y then ins_mem x a
      else if x = y then ()
      else ins_mem x b
    #pop-options

    val almostNode_sorted : #h:nat -> almostNode h -> bool
    let almostNode_sorted #h = function
    | LR a x b
    | RR a x b -> sorted (B a x b)
    | V root -> sorted root

    val hiddenTree_sorted : #h:nat -> hiddenTree h -> bool
    let hiddenTree_sorted #h = function
    | HB root
    | HR root -> sorted root

    val hiddenTree_max : #h:nat -> hiddenTree h -> option (nat * nat)
    let hiddenTree_max #h = function
    | HB root
    | HR root -> max root

    val hiddenTree_min : #h:nat -> hiddenTree h -> option (nat * nat)
    let hiddenTree_min #h = function
    | HB root
    | HR root -> min root

    val almostNode_max : #h:nat -> almostNode h -> option (nat * nat)
    let almostNode_max #h = function
    | LR a x b
    | RR a x b
    | V (R a x b)
    | V (B a x b) -> max (B a x b)
    | V Leaf -> None

    val almostNode_min : #h:nat -> almostNode h -> option (nat * nat)
    let almostNode_min #h = function
    | LR a x b
    | RR a x b
    | V (R a x b)
    | V (B a x b) -> min (B a x b)
    | V Leaf -> None

    val atLeast : (nat * nat) -> option (nat * nat) -> bool
    let atLeast x = function
    | Some y -> snd x <= snd y
    | None -> true

    val atMost : (nat * nat) -> option (nat * nat) -> bool
    let atMost x = function
    | Some y -> snd x >= snd y
    | None -> true

val global_upper_bound : #h:nat -> #c:color -> z:(nat * nat) -> s:rbnode h c ->
    Lemma 
    (requires atMost z (max s))
    (ensures  forall y. mem y s ==> snd y <= snd z)
    (decreases s)
    let rec global_upper_bound #h #c z = function
    | Leaf -> ()
    | R a y b
    | B a y b ->
      global_upper_bound z a;
      global_upper_bound z b


val global_lower_bound : #h:nat -> #c:color -> z:(nat * nat) -> s:rbnode h c {atLeast z (min s)} ->
    Lemma 
    (requires atLeast z (max s))
    (ensures  forall y. mem y s ==> snd y >= snd z)
    (decreases s)
    #set-options "--z3rlimit 100000"
    let rec global_lower_bound #h #c z = function
    | Leaf -> ()
    | R a y b
    | B a y b ->
      global_lower_bound z a;
      global_lower_bound z b

val mem_to_max : #h:nat -> #c:color -> z:(nat * nat) -> n:rbnode h c ->
    Lemma 
    (requires forall y. mem y n ==> snd y <= snd z) 
    (ensures  atMost z (max n)) 
    (decreases n)
    let rec mem_to_max #h #c z = function
    | Leaf -> ()
    | R a y b
    | B a y b ->
      mem_to_max z a;
      mem_to_max z b

    val mem_to_min : #h:nat -> #c:color -> z:(nat * nat) -> n:rbnode h c ->
    Lemma 
    (requires forall y. mem y n ==> snd y >= snd z) 
    (ensures  atLeast z (min n))
    (decreases n)
    let rec mem_to_min #h #c z = function
    | Leaf -> ()
    | R a y b
    | B a y b ->
      mem_to_min z a;
      mem_to_min z b

    val almostNode_mem_to_max : #h:nat -> z:(nat * nat) -> n:almostNode h ->
    Lemma 
    (requires forall y. almostNode_mem y n ==> snd y <= snd z) 
    (ensures  atMost z (almostNode_max n)) 
    (decreases n)
    let almostNode_mem_to_max #h z = function
    | V node -> mem_to_max z node
    | LR a x b
    | RR a x b -> mem_to_max z (B a x b)

    val almostNode_mem_to_min : #h:nat -> z:(nat * nat ) -> n:almostNode h ->
    Lemma 
    (requires forall y. almostNode_mem y n ==> snd y >= snd z)
    (ensures  atLeast z (almostNode_min n)) 
    (decreases n)
    let almostNode_mem_to_min #h z = function
    | V node -> mem_to_min z node
    | LR a x b
    | RR a x b -> mem_to_min z (B a x b)
    
    val hiddenTree_mem_to_max : #h:nat -> z:(nat * nat) -> n:hiddenTree h ->
    Lemma 
    (requires forall y. hiddenTree_mem y n ==> snd y <= snd z)
    (ensures  atMost z (hiddenTree_max n))
    (decreases n)
    let hiddenTree_mem_to_max #h z = function
    | HR node
    | HB node -> mem_to_max z node

    val hiddenTree_mem_to_min : #h:nat -> z:(nat * nat) -> n:hiddenTree h ->
    Lemma 
    (requires forall y. hiddenTree_mem y n ==> snd y >= snd z) 
    (ensures  atLeast z (hiddenTree_min n)) 
    (decreases n)
    let hiddenTree_mem_to_min #h z = function
    | HR node
    | HB node -> mem_to_min z node

    val ins_max : #h:nat -> #c:color -> z:(nat * nat) -> x:(nat * nat) -> s:rbnode h c -> t:almostNode h ->
    Lemma 
    (requires snd x <= snd z /\ atMost z (max s) /\ (forall y. mem y s \/ x = y <==> almostNode_mem y t)) 
    (ensures atMost z (almostNode_max t))
    let ins_max #h #c z x s t =
    global_upper_bound z s;
    almostNode_mem_to_max z t

    val ins_min : #h:nat -> #c:color -> z:(nat * nat) -> x:(nat * nat) -> s:rbnode h c -> t:almostNode h ->
    Lemma 
    (requires snd x >= snd z /\ atLeast z (min s) /\ (forall y. mem y s \/ x = y <==> almostNode_mem y t)) 
    (ensures atLeast z (almostNode_min t))
    let ins_min #h #c z x s t =
    global_lower_bound z s;
    almostNode_mem_to_min z t

    val insB_max : #h:nat -> #c:color -> z:(nat * nat) -> x:(nat * nat) -> s:rbnode h c -> t:hiddenTree h ->
    Lemma 
    (requires snd x <= snd z /\ atMost z (max s) /\ (forall y. mem y s \/ x = y <==> hiddenTree_mem y t))
    (ensures  atMost z (hiddenTree_max t))
    let insB_max #h #c z x s t =
    global_upper_bound z s;
    hiddenTree_mem_to_max z t

    val insB_min : #h:nat -> #c:color -> z:(nat * nat) -> x:(nat * nat) -> s:rbnode h c  -> t:hiddenTree h ->
    Lemma 
    (requires snd x >= snd z /\ atLeast z (min s) /\ (forall y. mem y s \/ x = y <==> hiddenTree_mem y t)) 
    (ensures  atLeast z (hiddenTree_min t))
    let insB_min #h #c z x s t =
    global_lower_bound z s;
    hiddenTree_mem_to_min z t
    

val balanceLB_preserves_sort : #h:nat -> #c:color -> a:almostNode h -> x:(nat * nat) -> b:rbnode h c ->
  Lemma 
  (requires almostNode_sorted a /\ sorted b /\ chain (almostNode_max a) x (min b))
  (ensures  hiddenTree_sorted (balanceLB a x b))
let balanceLB_preserves_sort #h #c left z d = ()

val balanceRB_preserves_sort : #h:nat -> #c:color -> a:rbnode h c -> x:(nat * nat) -> b:almostNode h ->
  Lemma 
  (requires sorted a /\ almostNode_sorted b /\ chain (max a) x (almostNode_min b))
  (ensures  hiddenTree_sorted (balanceRB a x b))
let balanceRB_preserves_sort #h #c a x right = ()

val balanceLR_preserves_sort : #h:nat -> #c:color -> a:hiddenTree h -> x:(nat * nat) -> b:rbnode h c ->
  Lemma 
  (requires hiddenTree_sorted a /\ sorted b /\ chain (hiddenTree_max a) x (min b))
  (ensures  almostNode_sorted (balanceLR a x b))
let balanceLR_preserves_sort #h #c a x b = ()

val balanceRR_preserves_sort : #h:nat -> #c:color -> a:rbnode h c -> x:(nat * nat) -> b:hiddenTree h ->
  Lemma 
  (requires sorted a /\ hiddenTree_sorted b /\ chain (max a) x (hiddenTree_min b))
  (ensures  almostNode_sorted (balanceRR a x b))
let balanceRR_preserves_sort #h #c a x b = ()


val ins_preserves_sort : #h:nat -> #c:color -> x:(nat * nat) -> s:rbnode h c ->
  Lemma 
  (requires sorted s) 
  (ensures  almostNode_sorted (ins x s)) 
  (decreases s)

val insB_preserves_sort : #h:nat -> x:(nat * nat) -> s:rbnode h Black ->
  Lemma 
  (requires sorted s) 
  (ensures  hiddenTree_sorted (insB x s)) 
  (decreases s)

let rec ins_preserves_sort #h #c x = function
  | Leaf -> ()
  | B a y b ->
    if snd x < snd y then
    begin
      ins_preserves_sort x a;
      ins_mem x a;
      ins_max y x a (ins x a);
      balanceLB_preserves_sort (ins x a) y b
    end
    else if x = y then ()
    else
    begin
      ins_preserves_sort x b;
      ins_mem x b;
      ins_min y x b (ins x b);
      balanceRB_preserves_sort a y (ins x b)
    end
  | R a y b ->
    if snd x < snd y then
    begin
      insB_preserves_sort x a;
      insB_mem x a;
      insB_max y x a (insB x a);
      balanceLR_preserves_sort (insB x a) y b
    end
    else if x = y then ()
    else
    begin
      insB_preserves_sort x b;
      insB_mem x b;
      insB_min y x b (insB x b);
      balanceRR_preserves_sort a y (insB x b)
    end
and insB_preserves_sort #h x = function
  | Leaf -> ()
  | B a y b ->
    if snd x < snd  y then
    begin
      ins_preserves_sort x a;
      ins_mem x a;
      ins_max y x a (ins x a);
      balanceLB_preserves_sort (ins x a) y b
    end
    else if x = y then ()
    else
    begin
      ins_preserves_sort x b;
      ins_mem x b;
      ins_min y x b (ins x b);
      balanceRB_preserves_sort a y (ins x b)
    end

val insert : (nat * nat) -> tree -> tree
  let insert x tree =
    ins_preserves_sort x tree.root;
    match ins x tree.root with
    | LR a x b
    | RR a x b
    | V (B a x b)
    | V (R a x b) -> RBTree (B a x b)

val insert_mem : x:(nat * nat) -> s:tree ->
    Lemma (forall y. mem y s.root \/ y = x <==> mem y (insert x s).root)
  let insert_mem x s = ins_mem x s.root*)

