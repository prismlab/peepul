module Orset_bst
open FStar.List.Tot

#set-options "--query_stats"

module O = Orset_space
open Library

type tree =
  |Leaf : tree
  |Node : (nat (*unique id*) * nat (*unique element*)) -> tree -> tree -> tree

val memt1 : (nat * nat) 
          -> tree 
          -> Tot bool
let rec memt1 x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> x = n || memt1 x t1 || memt1 x t2

val member_id_s : id:nat 
              -> t:tree
              -> Tot (b:bool {(exists ele. memt1 (id,ele) t) <==> b = true})
let rec member_id_s id t =
  match t with
  | Leaf -> false
  | Node (id1,_) t1 t2 -> id = id1 || member_id_s id t1 || member_id_s id t2

val member_ele_s : ele:nat 
               -> t:tree 
               -> Tot (b:bool {(exists id. memt1 (id,ele) t) <==> b = true})
let rec member_ele_s ele t =
  match t with
  | Leaf -> false
  | Node (_,ele1) t1 t2 -> ele = ele1 || member_ele_s ele t1 || member_ele_s ele t2

val forallt : p:((nat * nat) -> Tot bool)
            -> t:tree 
            -> Tot (r:bool{r = true <==> (forall x. memt1 x t ==> p x)})
let rec forallt p t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> p n && forallt p t1 && forallt p t2

val unique_id_s : t:tree -> Tot bool
let rec unique_id_s t =
  match t with
  |Leaf -> true
  |Node (id,ele) t1 t2 -> not (member_id_s id t1) && not (member_id_s id t2) &&
                         forallt (fun e -> not (member_id_s (fst e) t2)) t1 && 
                         forallt (fun e -> not (member_id_s (fst e) t1)) t2 &&
                         unique_id_s t1 && unique_id_s t2 

val unique_ele_s : t:tree -> Tot bool
let rec unique_ele_s t =
  match t with
  |Leaf -> true
  |Node (id,ele) t1 t2 -> not (member_ele_s ele t1) && not (member_ele_s ele t2) &&
                           forallt (fun e -> not (member_ele_s (snd e) t2)) t1 && 
                           forallt (fun e -> not (member_ele_s (snd e) t1)) t2 &&
                           unique_ele_s t1 && unique_ele_s t2

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

type s = tree1:tree {is_bst tree1 /\ unique_id_s tree1}

type rval = O.rval

val init : s
let init = Leaf

type op = O.op

val help : t1:s -> Lemma (ensures unique_ele_s t1)
                  [SMTPat (is_bst t1)]
#set-options "--z3rlimit 1000"
let rec help tr = 
  match tr with
  |Leaf -> ()
  |Node n t1 t2 -> help t1 ; help t2

val memt : ele:(nat * nat)
         -> t1:s
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
               (requires (is_bst t1 /\ unique_id_s t1))
               (ensures (fun r -> (forallt (ge r) t1) /\ memt1 r t1))
let rec find_max t1 =
  match t1 with
  | Node v _ t2 -> match t2 with
                  | Leaf -> v
                  | _ -> find_max t2

val delete_ele : x:nat
               -> t1:s
               -> Pure s
                 (requires true)
                 (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1) /\ snd e <> x) /\ not (member_ele_s x r) /\ 
                                   is_bst r /\ unique_id_s r)) 
                 (decreases (size t1))

#set-options "--z3rlimit 10000"
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

(*)val delete : x:(nat * nat)
           -> t1:t
           -> Pure t
             (requires (memt x t1))
             (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1) /\ e <> x) /\ not (memt x r) /\ is_bst r /\ unique_id r)) 
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
                     else Node n t1 (delete x t2)*)

#set-options "--z3rlimit 1000"
val update : ele:nat
           -> id:nat
           -> t1:s
           -> Pure tree
             (requires not (member_id_s id t1))
             (ensures (fun res -> (forall e. memt e t1 /\ snd e <> ele <==> memt1 e res /\ snd e <> ele) /\
                               (forall e. memt1 e res /\ fst e <> id /\ member_id_s (fst e) res <==> 
                                     memt e t1 /\ snd e <> ele /\ member_id_s (fst e) t1) /\
                               (forall e. member_ele_s e t1 \/ e = ele <==> member_ele_s e res) /\
                               (forall e. memt1 e res /\ e <> (id,ele) <==> memt e t1 /\ snd e <> ele) /\ 
                                     memt1 (id,ele) res /\ is_bst res /\ unique_id_s res))

#set-options "--z3rlimit 1000"
let rec update ele id tr =
  match tr with
  |Leaf -> Node (id,ele) Leaf Leaf
  |Node (id1,ele1) t1 t2 -> if ele = ele1 then Node (id, ele1) t1 t2
                              else if ele < ele1 then (Node (id1,ele1) (update ele id t1) t2)
                                 else Node (id1,ele1) t1 (update ele id t2)

let pre_cond_do s1 op = not (member_id_s (get_id op) s1)

let pre_cond_prop_do tr s1 op = true

val abs_dot : l1:O.s
            -> l2:O.s
            -> Pure O.s
              (requires (forall e. O.member_ele_s e l1 ==> not (O.member_ele_s e l2)) /\
                        (forall e. O.member_id_s e l1 ==> not (O.member_id_s e l2)))
              (ensures (fun res -> (forall e. mem e res <==> mem e l1 \/ mem e l2) /\
                                (forall e. O.member_id_s e res <==> O.member_id_s e l1 \/ O.member_id_s e l2) /\
                                (forall e. O.member_ele_s e res <==> O.member_ele_s e l1 \/ O.member_ele_s e l2)))
let rec abs_dot l1 l2 =
  match l1,l2 with
  |[],[] -> []
  |x::xs,_ -> x::(abs_dot xs l2)
  |[],_ -> l2

val flatten : tree1:s
            -> Pure O.s
              (requires true)
              (ensures (fun res -> (forall e. memt e tree1 <==> mem e res) /\
                                (forall e. member_ele_s e tree1 <==> O.member_ele_s e res) /\
                                (forall e. member_id_s e tree1 <==> O.member_id_s e res)))
              (decreases (size tree1))

#set-options "--z3rlimit 1000"
let rec flatten t =
  match t with
  |Leaf -> []
  |Node n t1 t2 -> assert ((forall e. O.member_ele_s e (flatten t1) ==> not (O.member_ele_s e (flatten t2))) /\
                          (forall e. O.member_id_s e (flatten t1) ==> not (O.member_id_s e (flatten t2))) /\
                           not (O.member_id_s (fst n) (flatten t1)) /\
                           not (O.member_ele_s (snd n) (flatten t1)) /\
                           not (O.member_id_s (fst n) (flatten t2)) /\
                           not (O.member_ele_s (snd n) (flatten t2)));
                  assert (not (O.member_id_s (fst n) (abs_dot (flatten t1) (flatten t2))) /\
                          not (O.member_ele_s (snd n) (abs_dot (flatten t1) (flatten t2))));
                  n::(abs_dot (flatten t1) (flatten t2))

val do : s1:s
       -> op1:(nat * op)
       -> Pure (s * rval)
         (requires pre_cond_do s1 op1)
         (ensures (fun res -> (O.opa op1 ==> (get_rval res = O.Bot) /\ (forall e. memt e s1 /\ snd e <> O.get_ele op1 <==> 
                                            memt e (get_st res) /\ snd e <> O.get_ele op1) /\
                           (forall e. memt e (get_st res) /\ fst e <> get_id op1 /\ member_id_s (fst e) (get_st res) <==> 
                                 memt e s1 /\ snd e <> O.get_ele op1 /\ member_id_s (fst e) s1) /\
                           (forall e. member_ele_s e s1 \/ e = O.get_ele op1 <==> member_ele_s e (get_st res)) /\
                           (forall e. memt e (get_st res) /\ e <> ((get_id op1), (O.get_ele op1)) <==> 
                                 memt e s1 /\ snd e <> O.get_ele op1) /\
                                 memt ((get_id op1), (O.get_ele op1)) (get_st res)) /\
                           (O.opr op1 ==> (get_rval res = O.Bot) /\ (forall e. memt e (get_st res) <==> memt e s1 /\ snd e <> O.get_ele op1)) /\ (get_op op1 = O.Rd ==> get_rval res = O.Val (O.get_set_s (flatten s1)) /\ get_st res = s1)))

let do s1 op =
  match op with
  |(_, O.Add _) -> (update (O.get_ele op) (get_id op) s1, O.Bot)
  |(_, O.Rem _) -> (delete_ele (O.get_ele op) s1, O.Bot)
  |(_, O.Rd) -> (s1, O.Val (O.get_set_s (flatten s1)))

val insert : x:(nat * nat)
           -> t1:s
           -> Pure tree
             (requires (not (memt x t1) /\ not (member_id_s (fst x) t1) /\ not (member_ele_s (snd x) t1)))
             (ensures (fun r -> is_bst r /\ (forall y. memt1 y r <==> (memt y t1 \/ x = y)) /\ unique_id_s r))
             (decreases (size t1))

#set-options "--z3rlimit 1000"
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then t
                      else if snd x < snd n then (let y = insert x t1 in Node n (insert x t1) t2)
                        else Node n t1 (insert x t2)

val totree1 : s1:O.s
            -> acc:s
            -> Pure s
              (requires (forall e. member_id_s e acc ==> not (O.member_id_s e s1)) /\
                        (forall e. member_ele_s e acc ==> not (O.member_ele_s e s1)))
              (ensures (fun t1 -> (forall e. memt e t1 <==> mem e s1 \/ memt e acc)))

#set-options "--z3rlimit 1000"
let rec totree1 l acc =
  match l with
  |[] -> acc
  |x::xs -> totree1 xs (insert x acc)

val totree : l:O.s -> t1:s {(forall e. memt e t1 <==> mem e l) /\
                           (forall e. member_ele_s e t1 <==> O.member_ele_s e l) /\
                           (forall e. member_id_s e t1 <==> O.member_id_s e l)}
let totree l = totree1 l Leaf

val lt : n1:(nat * nat) 
       -> n2:(nat * nat)
       -> Tot (b:bool)
let lt (id,ele) (id1,ele1) = (ele < ele1 && id <> id1)

val fst : (nat * nat) -> nat
let fst (id,ele) = id
val snd : (nat * nat) -> nat
let snd (id,ele) = ele

val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {(b = true <==> (forall e. memt e s1 ==> (forall a. mem a tr.l /\ O.opa a /\ snd e = O.get_ele a ==>
                                    (forall r. mem r tr.l /\ O.opr r /\ O.get_ele a = O.get_ele r /\ get_id a <> get_id r ==> 
                                     not (tr.vis a r)) ==> fst e >= get_id a) /\ 
                 (mem ((fst e), O.Add (snd e)) tr.l /\
  (forall r. mem r tr.l /\ O.opr r /\ O.get_ele r = snd e /\ fst e <> get_id r ==> not (tr.vis ((fst e), O.Add (snd e)) r)))) /\
                 (forall a. mem a tr.l /\ O.opa a ==> (forall r. mem r tr.l /\ O.opr r /\ O.get_ele a = O.get_ele r /\ get_id a <> get_id r ==> not (tr.vis a r)) ==> member_ele_s (O.get_ele a) s1))})

let sim tr s1 = O.sim tr (flatten s1)

val diff : a:s
         -> l:s
         -> Pure s
           (requires true)
           (ensures (fun d -> (forall e. memt e d <==> memt e a /\ not (memt e l)) /\
                           (forall e. memt e d /\ member_id_s (fst e) d <==> 
                                 memt e a /\ member_id_s (fst e) a /\ not (memt e l)) /\
                           (forall e. memt e d  /\ member_ele_s (snd e) d <==> 
                                 memt e a /\ member_ele_s (snd e) a /\ not (memt e l)) /\
                           (forall e. memt e a /\ memt e l ==> not (member_ele_s (snd e) d) /\ not (member_id_s (fst e) d))))
           (decreases %[l;a])
let diff a l =
  totree (O.diff (flatten a) (flatten l))

let pre_cond_merge l a b = O.pre_cond_merge (flatten l) (flatten a) (flatten b)
let pre_cond_prop_merge ltr l atr a btr b = true

val merge : l:s -> a:s -> b:s
           -> Pure s 
             (requires pre_cond_merge l a b)
             (ensures (fun res -> res = totree (O.merge (flatten l) (flatten a) (flatten b))))
let merge l a b = totree (O.merge (flatten l) (flatten a) (flatten b))

val prop_merge : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (pre_cond_merge l a b) /\ (sim (abs_merge ltr atr btr) (merge l a b)))

#set-options "--z3rlimit 1000"
let prop_merge ltr l atr a btr b =
  O.prop_merge ltr (flatten l) atr (flatten a) btr (flatten b)

val prop_do : tr:ae op
            -> st:s
            -> op:(nat * op)
            -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                              (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                    (ensures (sim (abs_do tr op) (get_st (do st op))))

#set-options "--z3rlimit 1000"
let prop_do tr st op =
  assert (not (member_id_s (get_id op) st));
  O.prop_do tr (flatten st) op

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. memt e a <==> memt e b))
let convergence tr a b =
  O.convergence tr (flatten a) (flatten b)

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (get_op op = O.Rd ==> (forall e. mem e (O.extract (get_rval (do st op))) <==>
                                               mem e (O.extract (O.spec op tr)))) /\
                               (get_op op <> O.Rd ==> (get_rval (do st op) = O.spec op tr)))
#set-options "--z3rlimit 1000"
let prop_spec tr st op = ()

instance orset_bst : mrdt s op rval = {
  Library.init = init;
  Library.spec = O.spec;   
  Library.sim = sim;
  Library.pre_cond_do = pre_cond_do;
  Library.pre_cond_prop_do = pre_cond_prop_do;
  Library.pre_cond_merge = pre_cond_merge;
  Library.pre_cond_prop_merge = pre_cond_prop_merge;
  Library.do = do;
  Library.merge = merge;
  Library.prop_do = prop_do;
  Library.prop_merge = prop_merge;
  Library.prop_spec = prop_spec;
  Library.convergence = convergence
}



(******************* Height-balanced BST ************************)

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
                                   (forall e. mem e r /\ O.member_id_s (fst e) r <==>
                                   mem e l /\ O.member_id_s (fst e) l /\ pos l e = pos1)))
                   (decreases %[(length l); pos1])
#set-options "--z3rlimit 10000000"
let rec take_element l n =
  match l with
  | h::t -> if n > 0 then take_element t (n-1) else [h]

val takemiddle : l:O.s
               -> Pure O.s
                 (requires (sorted l /\ length l >= 1))
                 (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e = length l/2) /\
                                 (forall e. mem e r /\ O.member_id_s (fst e) r <==> mem e l /\ 
                                 O.member_id_s (fst e) l /\ pos l e = length l/2)/\ length r = 1))
let takemiddle l = take_element l (length l/2)

val take : pos1:nat
         -> l:O.s
         -> Pure O.s
           (requires (pos1 < length l /\ sorted l))
           (ensures (fun r -> (forall e. mem e r <==> mem e l /\ pos l e < pos1) /\
                           (forall e. mem e r /\ O.member_id_s (fst e) r <==> 
                                 mem e l /\ O.member_id_s (fst e) l /\ pos l e < pos1) 
                            /\ O.unique_id_s r /\ length r = pos1 /\
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
                                (forall e. mem e r /\ O.member_id_s (fst e) r <==> 
                                      mem e l /\ O.member_id_s (fst e) l /\ pos l e < (length l/2)) 
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
                             (forall e. mem e r /\ O.member_id_s (fst e) r <==> 
                                   mem e l /\ O.member_id_s (fst e) l /\ pos l e >= pos1)
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
                               (forall e. mem e r /\ O.member_id_s (fst e) r <==> 
                                     mem e l /\ O.member_id_s (fst e) l /\ pos l e > (length l/2)) 
                                     /\ sorted r /\ length r = ((length l) - (length l)/2 - 1)))
               (decreases l)
let takeback l = drop (length l/2 + 1) l

val tree_of_list : l:O.s
                 -> Pure tree
                   (requires (sorted l))
                   (ensures (fun r -> (size r = length l) /\
                            (forall e. memt1 e r <==> mem e l)))
                   (decreases %[length l])

#set-options "--z3rlimit 1000000"
let rec tree_of_list l  =
  match l with
  | [] -> Leaf
  | h::[] -> Node h Leaf Leaf
  | h::t -> Node (hd (takemiddle l)) (tree_of_list (takefront l)) (tree_of_list (takeback l) )

