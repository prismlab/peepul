module Orset_bst

open FStar.List.Tot

type op =
    | Add
    | Rem

type o = (nat (*unique id*) * op * nat (*element*))

let get_id (id,_,_) = id
let get_op (_,op,_) = op
let get_ele (_,_,ele) = ele

type tree = 
    |Leaf : tree
    |Node : n:(nat * nat) -> tree -> tree -> tree
    
val memt1 : (nat * nat) -> tree -> Tot bool
let rec memt1 x t =
      match t with
      | Leaf -> false
      | Node n t1 t2 -> x = n || memt1 x t1 || memt1 x t2

val member_st : id:nat -> t:tree -> Tot (b:bool {(exists ele. memt1 (id,ele) t) <==> b = true})
let rec member_st id t =
      match t with
      | Leaf -> false
      | Node (id1,_) t1 t2 -> id = id1 || member_st id t1 || member_st id t2

val member_ele : ele:nat -> t:tree -> Tot (b:bool {(exists id. memt1 (id,ele) t) <==> b = true})
let rec member_ele ele t =
        match t with
        | Leaf -> false
        | Node (_,ele1) t1 t2 -> ele = ele1 || member_ele ele t1 || member_ele ele t2

val forallb : #a:eqtype 
            -> f:(a -> bool)
            -> l:list a 
            -> Tot(b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forallb #a f l =
    match l with
    |[] -> true
    |hd::tl -> if f hd then forallb f tl else false

val existsb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a 
            -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true})
let rec existsb #a f l =
    match l with
    |[] -> false
    |hd::tl -> if f hd then true else existsb f tl

val filter : #a:eqtype
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ f e})
let rec filter #a f l = 
        match l with
        |[] -> []
        |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

val member_s : id:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_s n l =
        match l with
        |[] -> false
        |(id,_)::xs -> (n = id) || member_s n xs

val unique_s : l:list (nat * nat)
             -> Tot bool
let rec unique_s l =
        match l with
        |[] -> true
        |(id,_)::xs -> not (member_s id xs) && unique_s xs
        
val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat) 
               -> Lemma (requires (unique_s l))
                       (ensures (unique_s (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
      match l with
      |[] -> ()
      |x::xs -> filter_uni f xs

type s = l:list (nat (*unique id*)* nat (*ele*)) {unique_s l}

val lt : n1:(nat * nat) 
       -> n2:(nat * nat)
       -> Tot (b:bool)
let lt (id,ele) (id1,ele1) =
       (ele < ele1 && id <> id1) || (ele = ele1 && id < id1)

val gt : n1:(nat * nat)
       -> n2:(nat * nat) 
       -> Tot (b:bool)
let gt (id,ele) (id1,ele1) = 
       (ele > ele1 && id <> id1) || (ele = ele1 && id > id1)

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

val is_bst : t:tree -> Tot (b:bool)
let rec is_bst t =
    match t with
    | Leaf -> true
    | Node n t1 t2 -> forallt (gt n) t1 && forallt (lt n) t2 && is_bst t1 && is_bst t2

val size : t1:tree -> Tot nat
let rec size t1 =
      match t1 with
      |Leaf -> 0
      |Node _ t1 t2 -> 1 + size t1 + size t2

type t = tree1:tree {is_bst tree1 /\ unique_st tree1}

val memt : ele:(nat * nat) -> t1:t -> Tot (b:bool {(memt1 ele t1 <==> b = true)})
let rec memt x t =
    match t with
    |Leaf -> false
    |Node n t1 t2 -> if x = n then true
                       else if lt x n then memt x t1
                         else  memt x t2

val except : #a:eqtype 
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ not (f e)})
let rec except #a f l =
  match l with
  |[] -> []
  |hd::tl -> if not (f hd) then hd::(except f tl) else except f tl

val member : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists n ele. mem (id,n,ele) l) <==> b=true})
let rec member n l =
  match l with
  |[] -> false
  |(id,_,_)::xs -> (n = id) || member n xs

val unique : l:list o
           -> Tot bool
let rec unique l =
  match l with
  |[] -> true
  |(id,_,_)::xs -> not (member id xs) && unique xs

noeq type ae  =
     |A : vis : (o -> o -> Tot bool)
        -> l:(list o) {(forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\ 
                      (forall e e'. (mem e l /\ mem e' l /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                      (forall e. mem e l ==> not (vis e e) (*irreflexive*) /\
                      (unique l))}  
        -> ae

val sim : tr:ae
        -> s1:s 
        -> Tot (bool) 
let  sim tr s1 =
     let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
     let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
     let lst = except (fun a -> (existsb (fun r -> get_ele r = get_ele a && tr.vis a r) lstr)) lsta in
     
     forallb (fun e -> mem ((get_id e), (get_ele e)) s1) lst &&
     forallb (fun e -> mem ((fst e), Add, (snd e)) lst) s1 

#set-options "--query_stats"              
val simt : tr:ae 
         -> t1:t
         -> Tot bool
let simt tr t1 =
    let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
    let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
    let lst = except (fun a -> (existsb (fun r -> get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

    forallb (fun e -> memt ((get_id e), (get_ele e)) t1) lst &&
    forallt (fun e -> mem ((fst e), Add, (snd e)) lst) t1
    
val insert : ele:(nat * nat) 
           -> tree1:t
           -> Pure t
             (requires not (member_st (fst ele) tree1))
             (ensures (fun res -> (memt ele res) /\ (forall e. memt e res <==> memt e tree1 \/ ele = e) /\
                               (forall e. member_st e res <==> member_st e tree1 \/ fst ele = e))) (decreases (size tree1))

#set-options "--z3rlimit 100"
let rec insert (id,ele) tr =
                   match tr with
                   | Leaf -> Node (id,ele) Leaf Leaf
                   | Node (id1,ele1) t1 t2 -> if (id,ele) = (id1,ele1) then tr 
                                             else if lt (id,ele) (id1,ele1) then (Node (id1,ele1) (insert (id,ele) t1) t2)
                                               else (Node (id1,ele1) t1 (insert (id,ele) t2))
                                                 
val totree1 : s1:s
            -> acc: t
            -> Pure t
              (requires (forall e. member_st e acc ==> not (member_s e s1)))
              (ensures (fun t1 -> (forall e. memt e t1 <==> mem e s1 \/ memt e acc)))
#set-options "--query_stats"
let rec totree1 l acc =
    match l with
    |[] -> acc
    |x::xs -> totree1 xs (insert x acc)

val totree : l:s -> t1:t {forall e. memt e t1 <==> mem e l}
let totree l = totree1 l Leaf
    
val rem1 : l:ae 
         -> op:o
         -> Pure (list o)
           (requires true)
           (ensures (fun r -> ((forall e. mem e r ==> mem e l.l) /\ (unique r)))) (decreases %[l.l])
let rec rem1 l op =
    match l with 
    |(A _ []) -> []
    |(A _ (x::xs)) -> if (x = op) then xs else (x::(rem1 (A l.vis xs) op))

val rem : l:ae 
        -> op:o
        -> Pure ae
          (requires true)
          (ensures (fun r -> ((forall e. mem e r.l ==> mem e l.l) /\
                          (forall e e1. mem e r.l /\ mem e1 r.l /\ r.vis e e1 ==> mem e l.l /\ mem e1 l.l /\ l.vis e e1) /\
                          (forall e e1. (mem e r.l /\ mem e1 r.l /\ not (r.vis e e1)) ==> (mem e l.l /\ mem e1 l.l /\ not (l.vis e e1))) /\
                          (forall e e1. (mem e r.l /\ mem e1 r.l /\ not (r.vis e e1 || r.vis e1 e)) ==> 
                                   (mem e l.l /\ mem e1 l.l /\ not (l.vis e e1 || l.vis e1 e))))))
let rem l op =
  let res = (rem1 l op) in
  (A (fun o o1 -> mem o l.l && mem o1 l.l && l.vis o o1) res)

val diff1 : a:ae
          -> l:ae
          -> Pure (list o)
            (requires (forall e. mem e l.l ==> mem e a.l) /\ 
                      (forall e e1. mem e l.l /\ mem e1 l.l /\ l.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                      (forall e e1. (mem e l.l /\ mem e1 a.l ==> mem e a.l /\ a.vis e e1)))
            (ensures (fun d -> (forall e. mem e d <==> mem e a.l /\ not (mem e l.l)) /\
                            (forall e. mem e d ==> not (member (get_id e) l.l)))) (decreases %[l.l;a.l])
let rec diff1 a l = 
    match a,l with
    |_,(A _ []) -> a.l
    |_,(A _ (x::xs)) -> if (mem x a.l) then (diff1 (rem a x) (A l.vis xs)) else (diff1 a (A l.vis xs))

val diff : a:ae
         -> l:ae
         -> Pure ae
          (requires (forall e. mem e l.l ==> mem e a.l) /\ 
                    (forall e e1. mem e l.l /\ mem e1 l.l /\ l.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                    (forall e e1. (mem e l.l /\ mem e1 a.l ==> mem e a.l /\ a.vis e e1)))
          (ensures (fun d -> (forall e. mem e d.l <==> mem e a.l /\ not(mem e l.l)) /\
                          (forall e. mem e d.l ==> not (member (get_id e) l.l)) /\
                          (forall e e1. mem e d.l /\ mem e1 d.l /\ d.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1)) ==> (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1))) /\
                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1 || d.vis e1 e)) ==>
                                   (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e))))) (decreases l)
let diff a l =
  (A (fun o o1 -> mem o a.l && mem o1 a.l && a.vis o o1) (diff1 a l))

val union1 : a:ae 
           -> b:ae
           -> Pure (list o)
             (requires (forall e. (mem e a.l ==> not (member (get_id e) b.l))) /\
                             (forall e. (mem e b.l ==> not (member (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l) /\
                             (unique u)))     (decreases %[a.l;b.l])
let rec union1 a b =
  match a,b with
  |(A _ []),(A _ []) -> []
  |(A _ (x::xs)),_ -> x::(union1 (A (fun o o1 -> mem o a.l && mem o1 a.l && a.vis o o1) xs) b)
  |(A _ []), (A _ (x::xs)) -> x::(union1 a (A (fun o o1 -> mem o b.l && mem o1 b.l && b.vis o o1) xs))

val union : a:ae 
          -> b:ae
          -> Pure ae
            (requires (forall e. (mem e a.l ==> not (member (get_id e) b.l))) /\
                            (forall e. (mem e b.l ==> not (member (get_id e) a.l))))
            (ensures (fun u -> (forall e. mem e u.l <==> mem e a.l \/ mem e b.l) /\
                            (forall e e1. (mem e u.l /\ mem e1 u.l /\ u.vis e e1) <==> 
                                     ((mem e a.l /\ mem e1 a.l /\ a.vis e e1) \/ (mem e b.l /\ mem e1 b.l /\ b.vis e e1))) /\
                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e) ==> 
                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1 || b.vis e1 e) ==> 
                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e))))
let union a b = 
  (A (fun o o1 -> (mem o a.l && mem o1 a.l && a.vis o o1) || (mem o b.l && mem o1 b.l && b.vis o o1)) (union1 a b))

val absmerge : l:ae
             -> a:ae
             -> b:ae
             -> Pure ae 
               (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                         (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> 
                                   mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\ mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                         (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                         (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                         (forall e. mem e (diff a l).l ==> not (member (get_id e) b.l)) /\
                         (forall e1. mem e1 (diff b l).l ==> not (member (get_id e1) a.l)))  
                (ensures (fun u ->(forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\ 
                               (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ u.vis e1 e2) <==> 
                                         (mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2) \/ 
                                         (mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2)) /\ 
                              (forall e e1. mem e l.l /\ mem e1 l.l /\ not (l.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e l.l /\ mem e1 l.l /\ not (l.vis e e1 || l.vis e1 e) ==> 
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                              (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e) ==>
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                              (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1 || b.vis e1 e) ==> 
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e))))
let absmerge l a b = 
    let la = diff a l in
    let lb = diff b l in
    let u1 = union la lb in
    let res = union l u1 in
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && b.vis o o1)) res.l)

val diff2 : a:s
          -> l:s
          -> Pure s
            (requires true)
            (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)))) (decreases %[a])
let rec diff2 a l = 
    filter (fun e -> not (mem e l)) a

val remove : l:s 
               -> ele:(nat * nat)
               -> Pure s 
               (requires true)
               (ensures (fun res -> (forall e. mem e res <==> mem e l /\ e <> ele)))
let rec remove l ele =
    match l with
    |[] -> []
    |x::xs -> if (x = ele) then xs else x::(remove xs ele)

val merge1 : l:s
           -> a:s 
           -> b:s 
           -> Pure s (requires (forall e. mem e (diff2 a l) ==> not (member_s (fst e) b)) /\
                              (forall e. mem e (diff2 b l) ==> not (member_s (fst e) a)))
                    (ensures (fun res -> (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                                      (mem e a /\ not (mem e l)) \/ (mem e b /\ not (mem e l)))))    (decreases %[l;a;b])

let rec merge1 l a b = 
      match l,a,b with
      |[],[],[] -> []
      |x::xs,_,_ -> if (mem x a && mem x b) then x::(merge1 xs (remove a x) (remove b x)) 
                    else if (mem x a && not (mem x b)) then (merge1 xs (remove a x) b)
                      else if (mem x b && not (mem x a)) then (merge1 xs a (remove b x))
                        else (merge1 xs a b)
      |[],x::xs,_ -> x::(merge1 [] xs b)
      |[],[],x::xs -> b

val merges : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                             (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                             (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                       (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                        mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                             (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))
                   (ensures (fun res -> true))                         
let merges ltr l atr a btr b = 
    merge1 l a b
    
val appendt : l1:s
                  -> l2:s
                  -> Pure s
                  (requires (forall e. mem e l1 ==> not (member_s (fst e) l2)) /\ (forall e. mem e l1 ==> not (mem e l2)))
                  (ensures (fun res -> (forall e. mem e res <==> mem e l1 \/ mem e l2) /\
                                    (forall e. member_s e res ==> member_s e l1 \/ member_s e l2)))
let rec appendt l1 l2 =
      match l1,l2 with
      |[],[] -> []
      |x::xs,_ -> x::(appendt xs l2)
      |[],_ -> l2
      
val flatten : tree1:t
            -> Pure s
              (requires true)
              (ensures (fun res -> (forall e. memt e tree1 <==> mem e res) )) (decreases (size tree1))                
let rec flatten t =
    match t with
    |Leaf -> []
    |Node n t1 t2 -> n::(appendt (flatten t1) (flatten t2))

val lemma1 : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Lemma (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                             (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                             (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                       (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                        mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                             (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))
                    (ensures (forall e. mem e (diff2 a l) ==> not (member_s (fst e) b)) /\
                             (forall e. mem e (diff2 b l) ==> not (member_s (fst e) a)))
#set-options "--z3rlimit 50"
let lemma1 ltr l atr a btr b = ()

val lemma2 : ltr:ae
          -> l:t
          -> atr:ae
          -> a:t 
          -> btr:ae
          -> b:t 
          -> Lemma (requires (simt ltr l /\ simt atr a /\ simt btr b) /\ 
                             (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                             (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                       (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                        mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                             (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))
                  (ensures (forall e. mem e (diff2 (flatten a) (flatten l)) ==> not (member_s (fst e) (flatten b))) /\
                           (forall e. mem e (diff2 (flatten b) (flatten l)) ==> not (member_s (fst e) (flatten a))))

#set-options "--z3rlimit 1000"
let lemma2 ltr l atr a btr b = 
  lemma1 ltr (flatten l) atr (flatten a) btr (flatten b); ()
(*114462 ms without lemma1*)
    
val merge : ltr:ae
          -> l:t
          -> atr:ae
          -> a:t
          -> btr:ae
          -> b:t
          -> Pure t (requires (simt ltr l /\ simt atr a /\ simt btr b) /\ 
                             (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                             (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                       (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                        mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                             (forall e. mem e (diff atr ltr).l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))
                   (ensures (fun res -> true)) 

let merge ltr l atr a btr b = 
  let m = merges ltr (flatten l) atr (flatten a) btr (flatten b) in
  totree m

val sim1 : tr:ae
         -> s1:s 
         -> Tot (bool) 
let rec sim1 tr s1 =
             let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
             let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
             let lst = except (fun a -> (existsb (fun r -> get_ele r = get_ele a && tr.vis a r) lstr)) lsta in
             forallb (fun e -> mem ((fst e), Add, (snd e)) lst) s1 

val sim2 : tr:ae
         -> s1:s 
         -> Tot (bool) 
let rec sim2 tr s1 =
             let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
             let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
             let lst = except (fun a -> (existsb (fun r -> get_ele r = get_ele a && tr.vis a r) lstr)) lsta in
             forallb (fun e -> mem ((get_id e), (get_ele e)) s1) lst
             
val prop_merge1s : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                                 (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                                 (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                           (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                           mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                                 (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))                        
                       (ensures (sim1 (absmerge ltr atr btr) (merges ltr l atr a btr b))) 

#set-options "--z3rlimit 10000"
let prop_merge1s ltr l atr a btr b = 
  lemma1 ltr l atr a btr b; ()

val prop_merge2s : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                                 (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                                 (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                           (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                           mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                                 (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))                        
                       (ensures (sim2 (absmerge ltr atr btr) (merges ltr l atr a btr b))) 

#set-options "--z3rlimit 10000"
let prop_merge2s ltr l atr a btr b = 
  lemma1 ltr l atr a btr b; ()
  
val prop_merges : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                                 (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                                 (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                           (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                           mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                                 (forall e. mem e (diff atr ltr).l  ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))                        
                       (ensures (sim (absmerge ltr atr btr) (merges ltr l atr a btr b))) 

let prop_merges ltr l atr a btr b = 
prop_merge1s ltr l atr a btr b;
prop_merge2s ltr l atr a btr b; ()

val prop_merge : ltr: ae
               -> l:t
               -> atr:ae
               -> a:t
               -> btr:ae
               -> b:t
               -> Lemma (requires (simt ltr l /\ simt atr a /\ simt btr b) /\ 
                                 (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                                 (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                           (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                           mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                                 (forall e. mem e (diff atr ltr).l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e (diff btr ltr).l ==> not (member (get_id e) atr.l)))
                       (ensures (simt (absmerge ltr atr btr) (merge ltr l atr a btr b)) )

let prop_merge ltr l atr a btr b = 
  prop_merges ltr (flatten l) atr (flatten a) btr (flatten b);
  ()

val ge : (nat * nat)-> (nat * nat) -> Tot bool
let ge n1 n2 = gt n1 n2 || n1 = n2

val find_max : t1:tree {Node? t1}
                         -> Pure (nat * nat)
                         (requires (is_bst t1) /\ unique_st t1)
                         (ensures (fun r -> (forallt (ge r) t1) /\ memt1 r t1))

let rec find_max t1 =
          match t1 with
          | Node v _ t2 -> match t2 with
                        | Leaf -> v
                        | _ -> find_max t2

val delete1 : x:(nat * nat)
            -> t1:t
            -> Pure t
              (requires true)
              (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1) /\ e <> x) /\ not (memt x r))) (decreases (size t1))

#set-options "--z3rlimit 10000"
let rec delete1 x tr = 
    match tr with
    | Leaf -> Leaf
    | Node n t1 t2 -> if n = x then
                         match t1, t2 with
                         | Leaf, Leaf -> Leaf
                         | _   , Leaf -> t1
                         | Leaf, _    -> t2
                         | _           -> assert (Node? t1); let y = find_max t1 in
                                          Node y (delete1 y t1) t2
                      else if lt x n then Node n (delete1 x t1) t2
                                    else Node n t1 (delete1 x t2)

val diff_t : a:t 
           -> l:s 
           -> Pure t
              (requires true)
              (ensures (fun r -> (forall e. memt e r <==> memt e a /\ not (mem e l))))  (decreases l)
let rec diff_t a l =
      match l with
      |[] -> a
      |x::xs -> if (memt x a) then diff_t (delete1 x a) xs else diff_t a xs

val delete : x:nat
           -> t1:t
           -> Pure t
                   (requires true)
                   (ensures (fun r -> (forall e. memt e r <==> memt e t1 /\ snd e <> x)  )) (decreases (size t1))
let delete x t1 =
        let t = flatten t1 in
        let lst = filter (fun e -> snd e = x) t in
        diff_t t1 lst
    

(*)
val le : (nat * nat)-> (nat * nat) -> Tot bool
let le n1 n2 = lt n1 n2 || n1 = n2

val find_min : t1:tree {Node? t1}
                      -> Pure (nat * nat)
                      (requires (is_bst t1) /\ unique_st t1)
                      (ensures (fun r -> (forallt (le r) t1) /\ memt1 r t1))

let rec find_min t1 =
         match t1 with
         | Node v t1 _ -> match t1 with
                       | Leaf -> v
                       | _ -> find_min t1

val delete : x:nat
           -> t1:t
           -> Div t
                (requires true)
                (ensures (fun r -> (forall e. memt1 e r <==> (memt e t1 /\ snd e <> x)) /\ not (member_ele x r))) (decreases (size t1))
                      
#set-options "--z3rlimit 100000"
let rec delete x tr = 
        match tr with
        | Leaf -> Leaf
        | Node n t1 t2 -> if snd n = x then
                            match t1, t2 with
                            | Leaf, Leaf -> Leaf
                            | _   , Leaf -> (delete x t1)
                            | Leaf, _    -> (delete x t2)
                            | _           -> assert (Node? t1 && Node? t2); 
                                              if  (member_ele x t1 && member_ele x t2) then let y = find_max t1 in
                                                     delete x (Node y (delete1 y t1) t2)
                                             else  if ((member_ele x t1) && not (member_ele x t2 )) then let b = find_min t2 in
                                                            Node b (delete x t1) (delete1 b t2)
                                               else if (not (member_ele x t1) && member_ele x t2) then let z = find_max t1 in
                                                       Node z (delete1 z t1) (delete x t2)
                                              
                                                          else let a = find_max t1 in
                                                            Node a (delete1 a t1) t2
                                                 
                         else if x < snd n then Node n (delete x t1) t2
                                         else Node n t1 (delete x t2)*)

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member (get_id op) tr.l)))
             (ensures (fun res -> true)) (decreases tr.l)
let append tr op =
     match tr with
     |(A _ []) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::[]))
     |(A _ (x::xs)) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::(x::xs)))
     
val app_op : s1:t
           -> op:o 
           -> Pure t
             (requires not (member_st (get_id op) s1))
             (ensures (fun res -> (get_op op = Add ==> (forall e. memt e res <==> memt e s1 \/ ((get_id op), (get_ele op)) = e) /\
                                                    (forall e. member_st e res <==> member_st e s1 \/ get_id op = e)) /\
                               (get_op op = Rem ==> (forall e. memt e res <==> memt e s1 /\ snd e <> get_ele op))))

let rec app_op s1 (id, op, ele) =
          match op with
          |Add -> insert (id,ele) s1
          |Rem -> delete ele s1
          
val prop_oper : tr:ae
              -> st:t
              -> op:o 
              -> Lemma (requires (simt tr st) /\ 
                                (not (member (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> (append tr op).vis e op))
                      (ensures (simt (append tr op) (app_op st op))) (decreases %[tr.l])                      
let prop_oper tr st op = ()

val convergence : tr:ae
                -> a:t
                -> b:t  
                -> Lemma (requires  (simt tr a /\ simt tr b))
                        (ensures (forall e. memt e a <==> memt e b))
let convergence tr a b = ()




(* Statistics: 
prop_merge (1st part) : sim1 
  let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
      let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
      let lst = except (fun a -> (existsb (fun r -> get_ele r = get_ele a && tr.vis a r) lstr)) lsta in
      forallb (fun e -> mem ((get_id e), (get_ele e)) s1) lst &&
      forallb (fun e -> mem ((fst e), Add, (snd e)) lst) s1 
      
348715 ms or 5.811 min (--z3rlimit 10000) for prop_merg1 and 
570098 ms or 9.50 min (--z3rlimit 10000) for prop_merge 

285852 ms for prop_merge_trial 
*)


  (*)val un2 : a:list (nat * nat)
         -> b:list (nat * nat)
         -> Pure (list (nat * nat))
                 (requires (unique_s a /\ unique_s b) /\ (forall e. mem e a ==> not (member_s (fst e) b)))
                 (ensures (fun res -> (forall e. mem e res <==> mem e a \/ mem e b) /\ unique_s res))
  let rec un2 a b =
              match a,b with
              |[],[] -> []
              |x::xs,_ -> x::(un2 xs b)
              |[],b -> b

  val inter : l:s 
            -> a:s 
            -> b:s
            -> Pure s
                    (requires (forall e. mem e (diff2 a l) ==> not (member_s (fst e) b)) /\
                              (forall e. mem e (diff2 b l) ==> not (member_s (fst e) a)))
                    (ensures (fun res -> (forall e. mem e res <==> mem e a /\ mem e b /\ mem e l) /\
                                      (forall e. member_s e res ==> member_s e l /\ member_s e a /\ member_s e b)))
  let rec inter l a b =
          filter (fun e -> mem e a && mem e b) l
          
  val sim0 : tr:ae 
          -> t1:t
          -> Tot bool             
  let rec sim0 tr t1 =
          let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
          let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
          let lst = except (fun a -> (existsb (fun r -> get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

          forallt (fun e -> mem ((fst e), Add, (snd e)) lst) t1 
          
  val sim1 : tr:ae 
           -> t1:t
           -> Tot bool             
  let rec sim1 tr t1 =
          let lsta = (filter (fun a -> (get_op a = Add)) tr.l) in
          let lstr = (filter (fun r -> (get_op r = Rem)) tr.l) in
          let lst = except (fun a -> (existsb (fun r -> get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

          forallb (fun e -> memt ((get_id e), (get_ele e)) t1) lst 
       
          
   val fold_tree : init:t -> f:((nat * nat) -> t -> t -> t) → t → Pure t (requires true) (ensures (fun r -> true))
  let rec fold_tree init f t =
  match t with
    |Leaf -> init
    |Node x t1 t2 -> f x (fold_tree init f t1) (fold_tree init f t2)

*)
