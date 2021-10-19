module Orset_bst_weak

open FStar.List.Tot
open Orset_weak

type tree = 
    |Leaf : tree
    |Node : n:(nat (*unique id*) * nat (*unique element*)) -> tree -> tree -> tree

#set-options "--query_stats"

val memt1 : (nat * nat) 
          -> tree 
          -> Tot bool
let rec memt1 x t =
    match t with
    | Leaf -> false
    | Node n t1 t2 -> x = n || memt1 x t1 || memt1 x t2

val member_st : id:nat 
              -> t:tree
              -> Tot (b:bool {(exists ele. memt1 (id,ele) t) <==> b = true})
let rec member_st id t =
    match t with
    | Leaf -> false
    | Node (id1,_) t1 t2 -> id = id1 || member_st id t1 || member_st id t2

val member_elet : ele:nat 
                -> t:tree 
                -> Tot (b:bool {(exists id. memt1 (id,ele) t) <==> b = true})
let rec member_elet ele t =
    match t with
    | Leaf -> false
    | Node (_,ele1) t1 t2 -> ele = ele1 || member_elet ele t1 || member_elet ele t2

val forallt : p:((nat * nat) -> Tot bool)
            -> t:tree 
            -> Tot (r:bool{r = true <==> (forall x. memt1 x t ==> p x)})
let rec forallt p t =
        match t with
        | Leaf -> true
        | Node n t1 t2 -> p n && forallt p t1 && forallt p t2

val unique_st : t:tree -> Tot bool
let rec unique_st t =
  match t with
  |Leaf -> true
  |Node (id,ele) t1 t2 -> not (member_st id t1) && not (member_st id t2) &&
                         forallt (fun e -> not (member_st (fst e) t2)) t1 && forallt (fun e -> not (member_st (fst e) t1)) t2 &&
                         unique_st t1 && unique_st t2 

val unique_elet : t:tree -> Tot bool
let rec unique_elet t =
    match t with
    |Leaf -> true
    |Node (id,ele) t1 t2 -> not (member_elet ele t1) && not (member_elet ele t2) &&
                           forallt (fun e -> not (member_elet (snd e) t2)) t1 && forallt (fun e -> not (member_elet (snd e) t1)) t2 &&
                           unique_elet t1 && unique_elet t2

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

type t = tree1:tree {is_bst tree1 /\ unique_st tree1}

val help : t1:t -> Lemma (ensures unique_elet t1)
                  [SMTPat (is_bst t1)]
#set-options "--z3rlimit 1000000"
let rec help tr = 
  match tr with
  |Leaf -> ()
  |Node n t1 t2 -> help t1 ; help t2

val memt : ele:(nat * nat) -> t1:t -> Tot (b:bool {(memt1 ele t1 <==> b = true)})
let rec memt x t =
  match t with
  |Leaf -> false
  |Node n t1 t2 -> if x = n then true
                     else if (snd x < snd n) then memt x t1
                         else memt x t2

val ge : (nat * nat)-> (nat * nat) -> Tot bool
let ge n1 n2 = (snd n1 > snd n2 && fst n1 <> fst n2) || n1 = n2

val find_max : t1:tree {Node? t1}
               -> Pure (nat * nat)
                 (requires (is_bst t1 /\ unique_st t1))
                 (ensures (fun r -> (forallt (ge r) t1) /\ memt1 r t1))
let rec find_max t1 =
      match t1 with
      | Node v _ t2 -> 
             match t2 with
             | Leaf -> v
             | _ -> find_max t2

val delete : x:nat
             -> t1:t
             -> Pure t
               (requires true)
               (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1) /\ snd e <> x) /\ not (member_elet x r) /\ is_bst r /\ unique_st r)) (decreases (size t1))

#set-options "--z3rlimit 1000000"
let rec delete x tr = 
          match tr with
          | Leaf -> Leaf
          | Node n t1 t2 -> if snd n = x then
                              match t1, t2 with
                              | Leaf, Leaf -> Leaf
                              | _   , Leaf -> t1
                              | Leaf, _    -> t2
                              | _           -> assert (Node? t1); let y = find_max t1 in
                                                     Node y (delete (snd y) t1) t2
                           else if x < snd n then Node n (delete x t1) t2
                                       else Node n t1 (delete x t2)

val delete1 : x:(nat * nat)
               -> t1:t
               -> Pure t
                 (requires (memt x t1))
                 (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1) /\ e <> x) /\ not (memt x r) /\ is_bst r /\ unique_st r)) (decreases (size t1))

#set-options "--z3rlimit 1000000"
let rec delete1 x tr = 
            match tr with
            | Leaf -> Leaf
            | Node n t1 t2 -> if  n = x then
                                match t1, t2 with
                                | Leaf, Leaf -> Leaf
                                | _   , Leaf -> t1
                                | Leaf, _    -> t2
                                | _           -> assert (Node? t1); let y = find_max t1 in
                                                       Node y (delete1 y t1) t2
                             else if snd x < snd n then Node n (delete1 x t1) t2
                                         else Node n t1 (delete1 x t2)

#set-options "--z3rlimit 1000000"
val update : ele:nat
           -> id:nat
           -> t1:t
           -> Pure tree
             (requires not (member_st id t1))
             (ensures (fun res -> (forall e. memt e t1 /\ snd e <> ele <==> memt1 e res /\ snd e <> ele) /\
                               (forall e. memt1 e res /\ fst e <> id /\ member_st (fst e) res <==> memt e t1 /\ snd e <> ele /\ member_st (fst e) t1) /\
                               (forall e. member_elet e t1 \/ e = ele <==> member_elet e res) /\
                               (forall e. memt1 e res /\ e <> (id,ele) <==> memt e t1 /\ snd e <> ele) /\ memt1 (id,ele) res /\
                               is_bst res /\ unique_st res))

#set-options "--z3rlimit 1000000"
let rec update ele id tr =
  match tr with
  |Leaf -> Node (id,ele) Leaf Leaf
  |Node (id1,ele1) t1 t2 -> if ele = ele1 then Node (id, ele1) t1 t2
                          else if ele < ele1 then (Node (id1,ele1) (update ele id t1) t2)
                                 else Node (id1,ele1) t1 (update ele id t2)
(*112095 ms*)

val app_op : s1:t
           -> op:o
           -> Pure t
             (requires (not (member_st (get_id op) s1)))
             (ensures (fun res -> (get_op op = Add ==> (forall e. memt e s1 /\ snd e <> get_ele op <==> memt e res /\ snd e <> get_ele op) /\
                               (forall e. memt e res /\ fst e <> get_id op /\ member_st (fst e) res <==> 
                                     memt e s1 /\ snd e <> get_ele op /\ member_st (fst e) s1) /\
                               (forall e. member_elet e s1 \/ e = get_ele op <==> member_elet e res) /\
                               (forall e. memt e res /\ e <> ((get_id op), (get_ele op)) <==> memt e s1 /\ snd e <> get_ele op) /\
                                            memt ((get_id op), (get_ele op)) res) /\
                               (get_op op = Rem ==> (forall e. memt e res <==> memt e s1 /\ snd e <> get_ele op))))

let app_op s1 (id, op, ele) =
          match op with
          |Add -> update ele id s1
          |Rem -> delete ele s1

val insert : x:(nat * nat)
               -> t1:t
               -> Pure tree
                 (requires (not (memt x t1) /\ not (member_st (fst x) t1) /\ not (member_elet (snd x) t1)))
                 (ensures (fun r -> is_bst r /\ (forall y. memt1 y r <==> (memt y t1 \/ x = y)) /\ unique_st r))
                 (decreases (size t1))

#set-options "--z3rlimit 1000000"
let rec insert x t =
      match t with
      | Leaf -> Node x Leaf Leaf
      | Node n t1 t2 -> if x = n then      t
                       else if snd x < snd n then
                         (let y = insert x t1 in 
                         Node n (insert x t1) t2)
                       else
                         Node n t1 (insert x t2)
                         
val totree1 : s1:s
            -> acc: t
            -> Pure t
              (requires (forall e. member_st e acc ==> not (member_s e s1)) /\
                        (forall e. member_elet e acc ==> not (member_ele e s1)))
              (ensures (fun t1 -> (forall e. memt e t1 <==> mem e s1 \/ memt e acc) (*)/\
                               (size t1 = size acc + length s1*)))

#set-options "--query_stats"
#set-options "--initial_fuel 10000000 --initial_ifuel 10000000"
#set-options "--z3rlimit 1000000"
let rec totree1 l acc =
    match l with
    |[] -> acc
    |x::xs -> totree1 xs (insert x acc)

val totree : l:s -> t1:t {(forall e. memt e t1 <==> mem e l) /\
                         (forall e. member_elet e t1 <==> member_ele e l) /\
                         (forall e. member_st e t1 <==> member_s e l) (*)/\
                         (size t1 = length l*)}
let totree l = totree1 l Leaf

val lt : n1:(nat * nat) 
       -> n2:(nat * nat)
       -> Tot (b:bool)
let lt (id,ele) (id1,ele1) =
        (ele < ele1 && id <> id1)

val appendt : l1:s
            -> l2:s
            -> Pure s
              (requires (forall e. member_ele e l1 ==> not (member_ele ( e) l2)) /\
                        (forall e. member_s e l1 ==> not (member_s ( e) l2)))
              (ensures (fun res -> (forall e. mem e res <==> mem e l1 \/ mem e l2) /\
                                (forall e. member_s e res <==> member_s e l1 \/ member_s e l2) /\
                                (forall e. member_ele e res <==> member_ele e l1 \/ member_ele e l2)))
let rec appendt l1 l2 =
    match l1,l2 with
    |[],[] -> []
    |x::xs,_ -> x::(appendt xs l2)
    |[],_ -> l2

val flatten : tree1:t
            -> Pure s
              (requires true)
              (ensures (fun res -> (forall e. memt e tree1 <==> mem e res) /\
                                (forall e. member_elet e tree1 <==> member_ele e res) /\
                                (forall e. member_st e tree1 <==> member_s e res)))
                                (decreases (size tree1))

#set-options "--z3rlimit 1000000"
let rec flatten t =
    match t with
    |Leaf -> []
    |Node n t1 t2 -> assert ((forall e. member_ele e (flatten t1) ==> not (member_ele ( e) (flatten t2))) /\
                            (forall e. member_s e (flatten t1) ==> not (member_s ( e) (flatten t2))) /\
                            not (member_s (fst n) ( (flatten t1) )) /\
                            not (member_ele (snd n) ( (flatten t1) )) /\
                            not (member_s (fst n) ( (flatten t2) )) /\
                            not (member_ele (snd n) ( (flatten t2) )));
                     assert (not (member_s (fst n) (appendt (flatten t1) (flatten t2))) /\
                             not (member_ele (snd n) (appendt (flatten t1) (flatten t2))));
                     n::(appendt (flatten t1) (flatten t2))

#set-options "--query_stats"
val simt : tr:ae
         -> s1:t
         -> Tot (b:bool {b = true <==> (forall a. memt a s1 ==> (mem ((fst a), Add, (snd a)) tr.l /\ 
                                     (forall r. mem r tr.l /\ get_op r = Rem ==>
                                     not (fst a <> get_id r && snd a = get_ele r && tr.vis ((fst a), Add, (snd a)) r)) /\
                (forall a1. mem a1 tr.l /\ get_op a1 = Add ==> 
                       not (fst a <> get_id a1 && snd a = get_ele a1 && tr.vis ((fst a), Add, (snd a)) a1)))) /\
                (forall a. (mem a tr.l /\ get_op a = Add /\ (forall r. mem r tr.l /\ get_op r = Rem ==>
                      not (get_id a <> get_id r && get_ele a = get_ele r && tr.vis a r))) ==> member_elet (get_ele a) s1) /\
                (forall a. memt a s1 ==> (mem ((fst a), Add, (snd a)) tr.l))})


#set-options "--z3rlimit 1000000"
let simt tr s1 = 
  let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
  let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
  let lst = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr) &&
                          not (existsb (fun a1 -> get_id a <> get_id a1 && get_ele a = get_ele a1 && tr.vis a a1) lsta)) lsta in
  let lst1 = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

  forallt (fun e ->  mem ((fst e), Add, (snd e)) lst) s1 &&
  forallb (fun e -> member_elet (get_ele e) s1) lst1

val difft : a:t
          -> l:t
          -> Pure t
            (requires true)
            (ensures (fun d -> (forall e. memt e d <==> memt e a /\ not (memt e l)) /\
                            (forall e. memt e d /\ member_st (fst e) d <==> 
                                  memt e a /\ member_st (fst e) a /\ not (memt e l)) /\
                            (forall e. memt e d  /\ member_elet (snd e) d <==> 
                                  memt e a /\ member_elet (snd e) a /\ not (memt e l)) /\
                            (forall e. memt e a /\ memt e l ==> not (member_elet (snd e) d))))
                            (decreases %[l;a])
let difft a l =
  totree (diff2 (flatten a) (flatten l))

val merget : ltr:ae
           -> l:t
           -> atr:ae
           -> a:t
           -> btr:ae
           -> b:t
           -> Pure t (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                              (simt ltr l /\ simt (union ltr atr) a /\ simt (union ltr btr) b) /\
                              (forall e. member_st e (difft a l) ==> not (member_st e (difft b l))) /\
                              (forall e. (memt e l /\ memt e a /\ memt e b) ==> 
                                    not (member_elet (snd e) (difft a l)) /\ not (member_elet (snd e) (difft b l)))) 
                     (ensures (fun res -> true))

#set-options "--z3rlimit 10000000"
let merget ltr l atr a btr b = 
    let m = merge ltr (flatten l) atr (flatten a) btr (flatten b) in
    totree m

#set-options "--z3rlimit 10000000"
val prop_merget : ltr: ae
                -> l:t
                -> atr:ae
                -> a:t
                -> btr:ae
                -> b:t
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (simt ltr l /\ simt (union ltr atr) a /\ simt (union ltr btr) b) /\
                                  (forall e. member_st e (difft a l) ==> not (member_st e (difft b l))) /\
                                  (forall e. (memt e l /\ memt e a /\ memt e b) ==> 
                                        not (member_elet (snd e) (difft a l)) /\ not (member_elet (snd e) (difft b l))))
                        (ensures (simt (absmerge ltr atr btr) (merget ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merget ltr l atr a btr b = 
  prop_merge ltr (flatten l) atr (flatten a) btr (flatten b);
  ()
(*122427 ms*)

val prop_opert : tr:ae
               -> st:t
               -> op:o 
               -> Lemma (requires (simt tr st) /\ 
                                 (not (member (get_id op) tr.l)) )
                       (ensures (simt (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_opert tr st op =
  assert (not (member_st (get_id op) st)); 
  prop_oper tr (flatten st) op;
  ()
 (*45366 ms*)

val convergence : tr:ae
                -> a:t
                -> b:t  
                -> Lemma (requires (simt tr a /\ simt tr b))
                        (ensures (forall e. member_elet e a <==> member_elet e b))
let convergence tr a b = ()

(******************* Height-balanced BST ***********************8*)

let max n1 n2 = if n1 > n2 then n1 else n2

val pos : l:s
        -> ele:(nat * nat)
        -> Pure nat
          (requires (mem ele l))
          (ensures (fun p -> true))
let rec pos l e =
  match l with
  |x::y -> if x = e then 0 else 1 + pos y e

val sorted : l:s
           -> Tot bool
             (decreases (length l))
let rec sorted l =
  match l with
  |[] -> true
  |x::[] -> true
  |x::y::xs -> snd x < snd y && sorted (y::xs)

val take_element : l:s
                   -> pos1:nat
                   -> Pure s
                     (requires (pos1 < length l) /\ length l >= 1 /\ sorted l)
                     (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e = pos1) /\ length r = 1 /\ sorted r /\
                              (forall e. mem e r /\ member_s (fst e) r <==> mem e l /\ member_s (fst e) l /\ pos l e = pos1)))
                     (decreases %[(length l); pos1])
#set-options "--z3rlimit 10000000"
let rec take_element l n =
  match l with
  | h::t -> if n > 0 then take_element t (n-1)
            else [h]

val takemiddle : l:s
                 -> Pure s
                   (requires (sorted l /\ length l >= 1))
                   (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e = length l/2) /\
                                   (forall e. mem e r /\ member_s (fst e) r <==> mem e l /\ member_s (fst e) l /\ pos l e = length l/2)/\ length r = 1))
let takemiddle l = 
    take_element l (length l/2)
    
val take : pos1:nat 
         -> l:s
         -> Pure s
           (requires (pos1 < length l /\ sorted l))
           (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e < pos1) /\
                           (forall e. mem e r /\ member_s (fst e) r <==> mem e l /\ member_s (fst e) l /\ pos l e < pos1) 
                            /\ unique_s r /\ length r = pos1 /\
                           (forall e. mem e r ==> pos l e < pos1))) (decreases %[pos1;l])
#set-options "--z3rlimit 10000000"
let rec take n l = 
  if n = 0 then [] else
   (match l with
     |h::t -> h:: take (n-1) t)

val takesorted : pos1:nat
               -> l:s
               -> Lemma (requires (pos1 < length l) /\ (sorted l))
                       (ensures (sorted (take pos1 l)))
                       (decreases %[pos1;(length l)])
#set-options "--z3rlimit 10000000"
let rec takesorted n l = 
    if n = 0 then () else
      match l with
      |[] -> ()
      |x::y -> takesorted (n - 1) y

val takefront : l:s
              -> Pure s
                (requires (sorted l /\ length l >= 1))
                (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e < (length l/2)) /\
                                (forall e. mem e r /\ member_s (fst e) r <==> mem e l /\ member_s (fst e) l /\ pos l e < (length l/2)) 
                                /\ sorted r /\ length r = (length l)/2))
                (decreases l)
#set-options "--z3rlimit 10000000"
let takefront l = 
  let t = take (length l/2) l in
  takesorted (length l/2) l;
  t

val drop : pos1:nat
         -> l:s
         -> Pure s
           (requires (pos1 <= length l /\ sorted l))
             (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e >= pos1) /\
                             (forall e. mem e r /\ member_s (fst e) r <==> mem e l /\ member_s (fst e) l /\ pos l e >= pos1)
                             /\ sorted r /\ length r = length l - pos1))
           (decreases %[pos1;l])  
let rec drop n l =
  if n = 0 then l else
    (match l with
     | h::t -> drop (n-1) t)

val takeback : l:s
             -> Pure s
               (requires (sorted l /\ length l >= 1))
               (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e > (length l/2)) /\
                               (forall e. mem e r /\ member_s (fst e) r <==> mem e l /\ member_s (fst e) l /\ pos l e > (length l/2)) 
                                /\ sorted r /\ length r = ((length l) - (length l)/2 - 1)))
               (decreases l)
let takeback l =
    drop (length l/2 + 1) l

val tree_of_list : l:s
                 -> Pure tree
                   (requires (sorted l))
                   (ensures (fun r -> (size r = length l) /\
                            (forall e. memt1 e r <==> mem e l)))
                 (decreases %[length l])

#set-options "--z3rlimit 1000000"
#set-options "--query_stats"
let rec tree_of_list l  =
  match l with
  | [] -> Leaf
  | h::[] -> Node h Leaf Leaf
  | h::t -> Node (hd (takemiddle l)) (tree_of_list (takefront l)) (tree_of_list (takeback l) )
(*92128*)




(*val merge1 : l:t
           -> a:t
           -> b:t
           -> Pure t
            (requires (forall e. member_st e (difft a l) ==> not (member_st e (difft b l))) /\
                      (forall e. (memt e l /\ memt e a /\ memt e b) ==> 
                             not (member_elet (snd e) (difft a l)) /\ not (member_elet (snd e) (difft b l))))
            (ensures (fun res -> (forall e. member_elet e res <==> (member_elet e l /\ member_elet e a /\ member_elet e b) \/ 
                              (member_elet e (difft a l) \/ member_elet e (difft b l))) /\ 
                              (forall e. memt e res <==> (memt e l /\ memt e a /\ memt e b) \/
                              (memt e (difft a l)) \/ (memt e (difft b l) /\ not (member_elet (snd e) (difft a l))))))
                              (decreases %[l;a;b])

#set-options "--z3rlimit 10000000"
let rec merge1 l a b = 
  match l,a,b with
    |Leaf, Leaf, Leaf -> Leaf
    |Node x t1 t2, _,_ -> if (memt x a && memt x b) then insert x (merge1 (delete1 x l) (delete1 x a) (delete1 x b)) 
                            else if (memt x a) then (merge1 (delete1 x l) (delete1 x a) b)
                              else if (memt x b) then (merge1 (delete1 x l) a (delete1 x b))
                                else (merge1 (delete1 x l) a b)
    |_,_, Node (id,ele) t1 t2 -> if (memt (id,ele) l) then merge1 (delete1 (id,ele) l)  a (delete1 (id,ele) b)
                                   else if (not (member_elet ele a)) then insert (id,ele) (merge1 Leaf a (delete1 (id,ele) b)) 
                                     else merge1 Leaf a (delete1 (id,ele) b)
    |Leaf,_,Leaf -> a*)
