module Fqueue

open FStar.List.Tot

#set-options "--query_stats"

type id = nat

type op =
  | Enqueue : nat -> op
  | Dequeue : (option (nat)) -> op

type o = (id * op)

let get_id (id, _) = id
let get_op (_, op) = op

val is_enqueue : v:o -> Tot (b:bool{(exists n. (get_op v = (Enqueue n))) <==> b = true})
let is_enqueue v = match v with
  | (_, Enqueue _) -> true
  | (_, Dequeue _) -> false

val is_dequeue : v:o -> Tot (b:bool{(exists x. get_op v = Dequeue x) <==> b = true})
let is_dequeue v = match v with
  | (_, Enqueue _) -> false
  | (_, Dequeue _) -> true

val get_ele : e:o{is_enqueue e} -> Tot (n:nat{e = (get_id e, (Enqueue n))})
let get_ele (id, Enqueue x) = x

val return : d:o{is_dequeue d} -> Tot (v:option (nat){d = (get_id d, (Dequeue v))})
let return (id, Dequeue x) = x

val mem_id : x:nat -> l:list (nat * nat) -> Tot (b:bool{(exists n. mem (x, n) l) <==> (b = true)})
let rec mem_id n l = match l with
  | [] -> false
  | (id, _)::xs -> (id = n) || (mem_id n xs)

val unique_id : l:list (nat * nat) -> Tot bool
let rec unique_id l = match l with
  | [] -> true
  | (id, _)::xs -> not (mem_id id xs) && unique_id xs

(* Return the position of a pair in a list of (nat * nat) pairs *)
val position : e:(nat * nat)
             -> s1:(list (nat* nat)) {mem e s1 /\ unique_id s1}
             -> Tot nat  (decreases (s1))
let rec position e s1 =
      match s1 with
      |x::xs -> if (e = x) then 0 else 1 + position e xs

(* Check if e1, different than e2, occurs before e2 in the list s1  *)
val order : e1:(nat * nat)
          -> e2:(nat * nat) {(fst e1) <> (fst e2)}
          -> s1:(list (nat * nat)) {mem e1 s1 /\ mem e2 s1 /\ unique_id s1}
          -> Tot (r:bool {(position e1 s1 < position e2 s1) <==> r = true})
let order e1 e2 s1 = (position e1 s1 < position e2 s1)

(* Represents the state of the MRDT. The UID is required to maintain the order of elements *)
type s =
    |S : ls : list (nat (* UID *) * nat (* value of the element *)) {unique_id ls} -> s

(* Return the last element of the list without removing it  *)
val peek : s1:s
         -> Pure (option (nat * nat))
                (requires true)
                (ensures (fun r -> (s1.ls = [] ==> r = None) /\
                                (s1.ls <> [] ==> (exists id n. r = Some (id, n)))))
let peek q =
  let n = q in
  match n with
  |(S []) -> None
  |(S (x::_)) -> Some x

val last_ele : l:(list (nat * nat)) {l <> []} -> (nat * nat)
let rec last_ele l = match l with
  | x::[] -> x
  | x::xs -> last_ele xs

val rear : s1:s
         -> Pure (option (nat * nat))
                (requires true)
                (ensures (fun r -> (s1.ls = []  ==> r = None) /\
                                (s1.ls <> [] ==> (r = Some (last_ele s1.ls)))))
let rear q =
  match q with
  |(S []) -> None
  |(S x) -> Some (last_ele x)

val memq : (nat * nat) -> s -> bool
let memq n q = (mem n q.ls)

val tolist : s1:s -> Tot (l:(list (nat * nat)) {unique_id l /\ s1 = S l})
let tolist (S l) = l

val rev_acc : l: list (nat * nat) -> acc: list (nat * nat) -> Tot (ls:list (nat * nat){(forall e. mem e l \/ mem e acc <==> mem e ls)})
let rec rev_acc l acc =
  match l with
      | [] -> acc
      | hd :: tl -> rev_acc tl (hd :: acc)

val rev : l:list (nat * nat) -> Tot (rl:list (nat * nat){forall e. mem e l <==> mem e rl})
let rev l = rev_acc l []

#set-options "--z3rlimit 1000000"

val ax0 : l1:list (nat * nat) -> l2:list (nat * nat) -> l3:list (nat * nat) -> Lemma (ensures ((l1 @ l2) @ l3 = l1 @ l2 @ l3))
let rec ax0 l1 l2 l3 = match l1 with
  | [] -> ()
  | x::xs -> ax0 xs l2 l3

val rev_acc0 : l1:list (nat * nat) -> l2:list (nat * nat) -> Lemma (ensures (rev_acc l1 l2 = (rev_acc l1 []) @ l2))
let rec rev_acc0 l1 l2 = match l1 with
  | [] -> ()
  | x::xs -> ax0 (rev xs) [x] l2; rev_acc0 xs l2;
           rev_acc0 xs [x]; rev_acc0 xs (x::l2)

val rev_app : l1:list (nat * nat){Cons? l1} -> Lemma (ensures ((rev (l1)) = (rev (tl l1)) @ (rev ([hd l1]))))
let rev_app l1 = match l1 with
  | [] -> ()
  | x::xs -> rev_acc0 (tl l1) [hd l1]

val rev_cor : l:list (nat * nat) -> Lemma (ensures (forall e. mem e l <==> mem e (rev l)))
let rec rev_cor l = match l with
  | [] -> ()
  | x::xs -> rev_cor xs

val rev_uni : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} -> Lemma (ensures (unique_id (x::l)))
let rec rev_uni l (id, v) = match l with
  | [] -> ()
  | (id1, _)::ys -> rev_uni ys (id, v)

val ax1 : l1:list (nat * nat){unique_id l1} -> l2:list (nat * nat){unique_id l2} -> x:(nat * nat){not (mem_id (fst x) l1) /\ not (mem_id (fst x) l2)}
          -> Lemma (ensures (not (mem_id (fst x) (l1 @ l2))))
let rec ax1 l1 l2 x = match l1 with
  | [] -> ()
  | y::ys -> ax1 ys l2 x

val app_uni : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} -> Lemma (ensures (unique_id (l @ [x])))
let rec app_uni l x = match l with
  | [] -> ()
  | y::ys -> app_uni ys x; ax1 ys [x] y

val rev2 : l:list (nat * nat){unique_id l} ->
         Lemma (ensures (l = [] \/ (rev l = ((rev (tl l)) @ [(hd l)]))))
let rec rev2 l = match l with
  | [] -> ()
  | x::xs -> rev2 xs; rev_app l;
         assert(xs = [] \/ rev xs = ((rev (tl xs)) @ [(hd xs)]))

val rev_unique : l:list (nat * nat){unique_id l} -> Lemma (ensures (unique_id (rev l)))
let rec rev_unique l = match l with
  | [] -> ()
  | x::xs -> rev_unique xs; app_uni (rev xs) x; rev2 l

val rev_unique1 : l:list (nat * nat){unique_id l} -> Lemma (ensures (unique_id l <==> unique_id (rev l)))
let rev_unique1 l = match l with
  | [] -> ()
  | x::xs -> rev_unique l

val empty_mem : l:list (nat * nat){unique_id l /\ l = []} -> Lemma (ensures (forall (x:(nat * nat)). not (mem_id (fst x) l)))
let empty_mem l = ()

val mem_sublist : l:list (nat * nat){unique_id l /\ Cons? l} -> x:(nat * nat){not (mem_id (fst x) l)} -> Lemma (ensures (not (mem_id (fst x) (tl l))))
let rec mem_sublist l x = match l with
  | x::[] -> empty_mem (tl l)
  | x::xs -> mem_sublist xs x

val mem_sl : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} -> 
             Lemma (ensures (Cons? l ==> (not (mem_id (fst x) (tl l))) /\ (l = [] ==> not (mem_id (fst x) l))))
let mem_sl l x = match l with
  | [] -> empty_mem l
  | l -> mem_sublist l x

val ax4 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} -> Lemma (ensures (unique_id (x::l)))

val ax5 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} -> 
          y:(nat * nat){(not (mem_id (fst y) l) /\ fst y <> fst x)} -> Lemma (ensures (not (mem_id (fst y) (l @ [x]))))
let rec ax5 l x y = match l with
  | [] -> ()
  | z::zs -> ax5 zs x y

val ax3 : l1:list (nat * nat){unique_id l1} -> x:(nat * nat){not (mem_id (fst x) l1)} -> Lemma (ensures (unique_id (l1 @ [x])))
let rec ax3 l1 x = match l1 with
  | [] -> ()
  | y::ys -> ax3 ys x; ax5 ys x y

val ax6 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} -> Lemma (ensures (forall e. ((mem e l \/ e = x) <==> mem e (l @ [x]))))
let rec ax6 l x = match l with
  | [] -> ()
  | y::ys -> if y = x then () else ax6 ys x

val ax7 : l:list (nat * nat) -> x:(nat * nat) -> Lemma (ensures (last_ele (l @ [x]) = x))
let rec ax7 l x = match l with
  | [] -> ()
  | y::ys -> ax7 ys x

val ax9 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} ->
          Lemma (ensures (forall e. (mem e l ==> (mem e (l @ [x]) /\ (unique_id (l @ [x])) /\ (mem x (l @ [x])) /\ order e x (l @ [x])))))
let rec ax9 l x = match l with
  | [] -> ()
  | y::ys -> ax9 ys x; ax3 l x; ax6 l x


val ax10 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} ->
           Lemma (ensures (forall e1 e2. mem e1 l /\ mem e2 l /\ fst e1 <> fst e2 /\ order e1 e2 l ==>
                              mem e1 (l @ [x]) /\ mem e2 (l @ [x]) /\ unique_id (l @ [x]) /\ order e1 e2 (l @ [x])))
let rec ax10 l x = match l with
  | [] -> ()
  | y::ys -> ax10 ys x; ax3 l x; ax6 l x

val enqueue : x:(nat * nat)
            -> s1:s
            -> Pure s
             (requires not (mem_id (fst x) (s1.ls)))
             (ensures (fun r -> true  /\ (forall e. (memq e s1 \/ e = x) <==> memq e r) /\ (rear r = Some x) /\
                         (forall e. memq e s1 ==> order e x r.ls) /\
                        (forall e e1. mem e s1.ls /\ mem e1 s1.ls /\ fst e <> fst e1 /\ order e e1 s1.ls ==> order e e1 r.ls)
                      ))
let enqueue x s1 =
  ax3 s1.ls x;
  ax6 s1.ls x;
  ax7 s1.ls x;
  ax9 s1.ls x;
  ax10 s1.ls x;
  (S ((s1.ls) @ [x]))

val dequeue : s1:s
            -> Pure ((option (nat * nat)) * s)
              (requires true)
              (ensures (fun r -> (forall e. memq e (snd r) <==> memq e s1 /\ Some e <> peek s1) /\
                              (s1.ls <> [] ==> length (snd r).ls = length s1.ls - 1) /\
                              (s1.ls = [] ==> length (snd r).ls = length s1.ls) /\
                   (forall e e1. mem e (snd r).ls /\ mem e1 (snd r).ls /\ fst e <> fst e1 /\ order e e1 (snd r).ls ==> order e e1 (tolist s1))
                   ))
let dequeue q =
  match q with
  |(S []) -> (None, q)
  |(S (x::xs)) -> (Some x, (S xs))


val get_val : a:option (nat * nat){Some? a} -> n:nat{exists b. a = Some(n, b)}
let get_val a = match a with
  | Some (x, y) -> x

val app_op : s1:s
           -> op:o
           -> Pure s
             (requires (not (mem_id (get_id op) s1.ls)))
             (ensures (fun r ->
                         (is_enqueue op ==> ((forall e. (memq e s1 \/ e = (get_id op, get_ele op)) <==> memq e r) /\ (rear r = Some (get_id op, get_ele op)) /\
                         (forall e. memq e s1 ==> order e (get_id op, get_ele op) r.ls) /\
                         (forall e e1. mem e s1.ls /\ mem e1 s1.ls /\ fst e <> fst e1 /\ order e e1 s1.ls ==> order e e1 r.ls))) /\
                         (is_dequeue op ==> ((forall e. memq e r <==> memq e s1 /\ Some e <> peek s1) /\
                         (s1.ls <> [] ==> length r.ls = length s1.ls - 1) /\ (s1.ls = [] ==> length r.ls = length s1.ls) /\
                         (forall e e1. mem e r.ls /\ mem e1 r.ls /\ fst e <> fst e1 /\ order e e1 r.ls ==> order e e1 s1.ls))) /\
                         (exists n. get_op op = (Enqueue n) ==> (exists id. rear r = (Some (id,n)))) /\
                         (s1.ls <> [] /\ is_dequeue op ==> not (mem_id (get_val (peek s1)) r.ls)) /\
                         (s1.ls = [] /\ is_dequeue op ==> r.ls = [])
                      ))
let app_op s e =
  match e with
  | (id, Enqueue n) -> enqueue (id,n) s
  | (_, Dequeue x) -> snd (dequeue s)

val member : id:nat
           -> l:list o
           -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member n xs

val unique : l:list o
           -> Tot bool
let rec unique l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member id xs) && unique xs

noeq type ae =
     |A : vis:(o -> o -> Tot bool) -> l:list o {unique l} -> ae

assume val axiom_ae : l:ae
                   -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\
                           get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*) /\
                           (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                           (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*) ))
                           [SMTPat (unique l.l)]

val pos : e1:o -> l:list o{unique l /\ mem e1 l} -> Tot nat
let rec pos e1 l = match l with
| x::xs -> if x = e1 then 0 else 1 + (pos e1 xs)

val matched : e:o{is_enqueue e} -> d:o{is_dequeue d} -> tr:ae{mem e tr.l /\ mem d tr.l} -> Tot (b:bool{(return d = Some (get_ele e) /\ (tr.vis e d)) <==> (b = true)})
let matched e d tr = (return d = Some (get_ele e)) && (tr.vis e d)

val sub_list : e:o -> l:list o{mem e l /\ unique l} -> l1:list o{not (mem e l1) /\ unique l1 /\ (forall e. mem e l1 ==> mem e l) /\ length l1 <= length l}
let rec sub_list e l = match l with
  | x::xs -> if x = e then xs else sub_list e xs

val position_o : e:o
             -> s1:(list o) {mem e s1 /\ unique s1}
             -> Tot nat  (decreases (s1))
let rec position_o e s1 =
      match s1 with
      |x::xs -> if (e = x) then 0 else 1 + (position_o e xs)

val ord : e1:o
          -> e2:o {(fst e1) <> (fst e2)}
          -> s1:(list o) {mem e1 s1 /\ mem e2 s1 /\ unique s1}
          -> Tot (r:bool {(position_o e1 s1 < position_o e2 s1) <==> r = true})
let ord e1 e2 s1 = (position_o e1 s1 < position_o e2 s1)

val ob : e:o -> d:o{fst e <> fst d} -> l:list o{mem e l /\ mem d l /\ unique l} -> Tot (b:bool{ord e d l <==> b = true})
let rec ob e d l = match l with
  | x::xs -> if x = e then mem d xs else 
           (if x <> d then ob e d xs else false)
 
val max : x:int -> y:int -> Tot (z:int{z >= x /\ z >= y})
let max x y = if x > y then x else y

val len_del : l:list o{unique l} -> Tot int
let rec len_del l = match l with
  | [] -> 0
  | x::xs -> if (is_enqueue x) then 1 + (len_del xs) else ((-1) + len_del xs)

val is_empty : s1:s -> Tot (b:bool{s1.ls = [] <==> b = true})
let is_empty s = (s.ls = [])

val is_empty' : l:list o{unique l} -> s1:s -> Tot bool
let is_empty' l s1 = ((length s1.ls) + (len_del l) = 0)

val filter_s : f:((nat * nat) -> bool)
           -> l:list (nat * nat) {unique_id l}
           -> Tot (l1:list (nat * nat) {(forall e. mem e l1 <==> mem e l /\ f e) /\ unique_id l1}) (decreases l)
let rec filter_s f l =
    match l with
    |[] -> []
    |hd::tl -> if f hd then hd::(filter_s f tl) else filter_s f tl

val filter_op : f:(o -> bool)
           -> l:list o
           -> Tot (l1:list o {(forall e. mem e l1 <==> (mem e l /\ f e))})
let rec filter_op f l =
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter_op f tl) else filter_op f tl

val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat)
               -> Lemma (requires (unique_id l))
                       (ensures (unique_id (filter f l)) /\ (forall e. mem e (filter f l) <==> mem e l /\ f e) /\
                                (forall e e1. fst e <> fst e1 /\ mem e (filter f l) /\ mem e1 (filter f l) /\ order e e1 (filter f l) <==>
                                           mem e l /\ mem e1 l  /\ order e e1 l /\ f e /\ f e1))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
          match l with
          |[] -> ()
          |x::xs -> filter_uni f xs

val count_enqueue : tr:(list o) -> nat
let rec count_enqueue tr =
  match tr with
  |[] -> 0
  |(id,(Enqueue _))::xs -> 1 + count_enqueue xs
  |(id,_)::xs -> count_enqueue xs

val count_deqeueue : tr:(list o) -> nat
let rec count_dequeue tr =
    match tr with
    |[] -> 0
    |(id,(Dequeue _))::xs -> 1 + count_dequeue xs
    |(id,_)::xs -> count_dequeue xs

val forall_mem : #t:eqtype
             -> l:list t
             -> f:(t -> bool)
             -> Tot(b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forall_mem l f =
       match l with
       | [] -> true
       | hd::tl -> if f hd then forall_mem tl f else false

val exists_mem : #t:eqtype
            -> l:list t
            -> f:(t -> bool)
            -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true})
let rec exists_mem l f =
  match l with
  | [] -> false
  | hd::tl -> if f hd then true else exists_mem tl f

val sim0 : tr:ae
        -> s0:s
        -> Tot(b:bool{b = true <==>
                       ((forall e. memq e s0 <==> (exists e1. mem e1 tr.l /\ is_enqueue e1 /\ e = (get_id e1, get_ele e1) /\
                                   (forall e2. mem e2 tr.l /\ is_dequeue e2 ==> (not (matched e1 e2 tr))))
                        )
                      )})
let sim0 tr s0 =
    axiom_ae tr;
    let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && matched x d tr))) tr.l in
    if forall_mem enq_list (fun x -> mem x tr.l && is_enqueue x && mem ((get_id x), (get_ele x)) (s0.ls)) &&
    forall_mem (s0.ls) (fun x -> mem ((fst x), Enqueue (snd x)) enq_list)
                            then true else false

val sim1 : tr:ae
        -> s0:s
        -> Tot(b:bool{b = true <==> (forall (e1 e2:(nat * nat)). (memq e1 s0 /\ memq e2 s0 /\ get_id e1 <> get_id e2 /\ order e1 e2 s0.ls) <==>
                          (exists (e e0:o). mem e tr.l /\ mem e0 tr.l /\ is_enqueue e /\ is_enqueue e0 /\ (get_id e <> get_id e0) /\
                                 (forall e3. mem e3 tr.l /\ is_dequeue e3 ==> (not (matched e e3 tr)) /\ (not (matched e0 e3 tr))) /\
                                (e1 = (get_id e, get_ele e)) /\ (e2 = (get_id e0, get_ele e0)) /\ tr.vis e e0)
                      )})
let sim1 tr s0 =
    axiom_ae tr;
    let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l &&
                                    not (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && matched x d tr))) tr.l in
    if forall_mem s0.ls (fun x -> memq x s0 &&
       (forall_mem (filter_s (fun z -> fst x <> fst z && mem x s0.ls && mem z s0.ls && order x z s0.ls) s0.ls)
                     (fun y -> (fst y <> fst x && mem ((fst x), Enqueue (snd x)) enq_list) &&
                       (mem ((fst y), Enqueue (snd y)) enq_list) && (tr.vis ((fst x), Enqueue (snd x)) ((fst y), Enqueue (snd y))))
                         )) &&
       forall_mem enq_list (fun e1 -> mem e1 enq_list &&
              (forall_mem (filter_op (fun p -> mem p enq_list && get_id p <> get_id e1) enq_list)
                            (fun e2 -> mem e2 enq_list &&
                             (if tr.vis e1 e2 then
                                 (if (get_id e1 <> get_id e2 && mem ((get_id e1), (get_ele e1)) (s0.ls) && mem ((get_id e2), (get_ele e2)) (s0.ls)
                                   && order ((get_id e1), (get_ele e1)) ((get_id e2), (get_ele e2)) (s0.ls)) then true else false) else true))
                                    ))
                            then true else false

val sim : tr:ae
        -> s0:s
        -> Tot(b:bool{b = true <==>
                       ((forall e. memq e s0 <==> (exists e1. mem e1 tr.l /\ is_enqueue e1 /\ e = (get_id e1, get_ele e1) /\
                                   (forall e2. mem e2 tr.l /\ is_dequeue e2 ==> (not (matched e1 e2 tr))))
                        ) /\ (forall (e1 e2:(nat * nat)). (memq e1 s0 /\ memq e2 s0 /\ get_id e1 <> get_id e2 /\ order e1 e2 s0.ls) <==>
                          (exists (e e0:o). mem e tr.l /\ mem e0 tr.l /\ is_enqueue e /\ is_enqueue e0 /\ (get_id e <> get_id e0) /\
                                 (forall e3. mem e3 tr.l /\ is_dequeue e3 ==> (not (matched e e3 tr)) /\ (not (matched e0 e3 tr))) /\
                                (e1 = (get_id e, get_ele e)) /\ (e2 = (get_id e0, get_ele e0)) /\ tr.vis e e0))
                      )})
let sim tr s0 = sim0 tr s0 && sim1 tr s0

val append : tr:ae
             -> op:o
             -> Pure ae
               (requires (not (member (get_id op) tr.l)))
               (ensures (fun res -> (forall e. mem e res.l <==> (mem e tr.l \/ e = op)) /\
                        (forall e1 e2. mem e1 tr.l /\ mem e2 tr.l /\ get_id e1 <> get_id e2 /\ tr.vis e1 e2 ==> res.vis e1 e2) /\
                        (forall e. mem e tr.l ==> res.vis e op)))
let append tr op =
    match tr with
    |(A _ ops) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                              (mem o tr.l && o1 = op && get_id o <> get_id op)) (op::ops))

val union_list_ae : l:ae
           -> a:ae
           -> Pure (list o)
             (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique u))) (decreases %[l.l;a.l])
let rec union_list_ae l a =
  match l,a with
  |(A _ []), (A _ []) -> []
  |(A _ (x::xs)), _ -> x::(union_list_ae (A l.vis xs) a)
  |(A _ []), (A _ (x::xs)) -> x::(union_list_ae l (A a.vis xs))

val union : l:ae
          -> a:ae
          -> Pure ae
            (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))))
            (ensures (fun u -> (forall e e1. (mem e u.l /\ mem e1 u.l /\ get_id e <> get_id e1 /\ u.vis e e1) <==>
                                     (mem e l.l /\ mem e1 l.l /\ get_id e <> get_id e1 /\ l.vis e e1) \/
                                     (mem e a.l /\ mem e1 a.l /\ get_id e <> get_id e1 /\ a.vis e e1) \/
                                     (mem e l.l /\ mem e1 a.l /\ get_id e <> get_id e1))))
let union l a =
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1)) (union_list_ae l a))

val absmerge_list_ae : l:ae
              -> a:ae
              -> b:ae
              -> Pure (list o)
                (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                          (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                          (forall e. mem e l.l ==> not (member (get_id e) b.l)))
                (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique u))) (decreases %[l.l;a.l;b.l])
let rec absmerge_list_ae l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> []
  |(A _ (x::xs)), _, _ -> x::(absmerge_list_ae (A l.vis xs) a b)
  |(A _ []), (A _ (x::xs)), _ -> x::(absmerge_list_ae l (A a.vis xs) b)
  |(A _ []), (A _ []), (A _ (x::xs)) -> x::(absmerge_list_ae l a (A b.vis xs))

val absmerge : l:ae
             -> a:ae
             -> b:ae
             -> Pure ae
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                         (forall e. mem e l.l ==> not (member (get_id e) b.l)))
               (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                               (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2) <==>
                                         (mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/
                                         (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ (union l a).vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ (union l b).vis e1 e2))))
let absmerge l a b =
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) ||
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1 && (union l a).vis o o1) ||
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1 && (union l b).vis o o1)) (absmerge_list_ae l a b))

val diff_s : a:list (nat * nat)
           -> l:list (nat * nat)
           -> Pure (list (nat * nat))
             (requires (unique_id a /\ unique_id l))
             (ensures (fun d -> (forall e. mem e d <==> (mem e a /\ not (mem e l))) /\ unique_id d ))
let diff_s a l = filter_s (fun e -> not (mem e l)) a

val intersection : l:list (nat * nat)
                 -> a:list (nat * nat)
                 -> b:list (nat * nat)
                 -> Pure (list (nat * nat))
                    (requires unique_id l /\ unique_id a /\  unique_id b /\
                              (forall e. mem e (diff_s a l) ==> not (mem_id (fst e) b)) /\
                              (forall e. mem e (diff_s b l) ==> not (mem_id (fst e) a)))
                    (ensures (fun i -> (forall e. mem e i <==> mem e a /\ mem e b /\ mem e l) /\ unique_id i /\
                                    (forall e. mem_id e i ==> mem_id e l /\ mem_id e a /\ mem_id e b) /\
                                    (forall e e1. mem e l /\ mem e1 l /\ fst e <> fst e1 /\ order e e1 l /\
                                      mem e a /\ mem e1 a /\ mem e b /\ mem e1 b <==> mem e i /\ mem e1 i /\ order e e1 i)))
let intersection l a b =
          filter (fun e -> mem e a && mem e b) l


val union_s : a:list (nat * nat)
            -> b:list (nat * nat)
            -> Pure (list (nat * nat))
              (requires unique_id a /\ unique_id b /\ (forall e. mem e a ==> not (mem_id (fst e) b)))
              (ensures (fun u -> (forall e. mem e u <==> mem e a \/ mem e b) /\ unique_id u /\
                              (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ order e e1 a ==> order e e1 u) /\
                              (forall e e1. mem e b /\ mem e1 b /\ fst e <> fst e1 /\ order e e1 b ==> order e e1 u) /\
                              (forall e e1. mem e a /\ mem e1 b /\ fst e <> fst e1 ==> order e e1 u)))
let rec union_s a b =
match a,b with
  |[],[] -> []
  |x::xs,_ -> x::(union_s xs b)
  |[], x::xs -> x::(union_s [] xs)

val merge_state : l:list (nat * nat)
                -> a:list (nat * nat)
                -> b:list (nat * nat)
                -> Pure (list (nat * nat))
                  (requires unique_id a /\ unique_id l /\ unique_id b /\
                            (forall e. mem e (diff_s a l) ==> not (mem_id (fst e) b)) /\
                            (forall e. mem e (diff_s b l) ==> not (mem_id (fst e) a)))
                  (ensures (fun res -> unique_id res /\ (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/
                                    (mem e a /\ not (mem e l)) \/ (mem e b /\ not (mem e l))) /\
                                    (forall e. mem e l /\ not (mem e a) ==> not (mem e res)) /\
                                    (forall e. mem e l /\ not (mem e b) ==> not (mem e res)) /\
                                    (forall e e1. mem e l /\ mem e1 l /\ fst e <> fst e1 /\ order e e1 l /\ mem e res /\ mem e1 res ==> order e e1 res)))
let merge_state l a b =
  let ixn = intersection l a b in
  let diff_a = diff_s a l in
  let diff_b = diff_s b l in
  let union_ab = union_s diff_a diff_b in
  union_s ixn union_ab

val eff_enq : tr:ae
            -> Pure (list o)
            (requires true)
            (ensures (fun r -> forall_mem r (fun x -> is_enqueue x && mem x tr.l && not
                                     (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && matched x d tr)))))
let eff_enq tr = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                                     (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && matched x d tr))) tr.l

#push-options "--initial_fuel 10 --ifuel 10 --initial_ifuel 10 --fuel 10 --z3rlimit 10000000000"

val eff_enq0 : tr:ae
             -> op:o{(not (member (get_id op) tr.l))}
             -> Lemma (ensures ((is_enqueue op ==> (eff_enq (append tr op) = op::(eff_enq tr))) /\
                              (Cons? (eff_enq tr) /\ is_dequeue op ==> (((hd (eff_enq tr))::(eff_enq (append tr op))) = (eff_enq tr))) /\
                              ((eff_enq tr = []) /\ is_dequeue op ==> (eff_enq (append tr op) = [])))) (decreases (tr.l))
let rec eff_enq0 tr op = match tr with
  | A _ [] -> ()
  | A vis (x::xs) -> eff_enq0 (A (fun o o1 -> mem o xs && mem o1 xs && vis o o1) xs) x;
                   // assert((is_enqueue op ==> (eff_enq (append tr op) = op::(eff_enq tr))));
                   // assert((Cons? (eff_enq tr) /\ is_dequeue op ==> (((hd (eff_enq tr))::(eff_enq (append tr op))) = (eff_enq tr))));
                   // assert(((eff_enq tr = []) /\ is_dequeue op ==> (eff_enq (append tr op) = [])));
                   admit()


val prop_oper0: tr:ae
                -> st:s
                -> op:o
                -> Lemma (requires (sim0 tr st) /\ (not (member (get_id op) tr.l)))
                         (ensures (sim0 (append tr op) (app_op st op)))

let prop_oper0 tr st op = match tr with
  | A _ [] -> ()
  | A _ (x::xs) -> match op with
    | (id, Enqueue x) -> let ax = append tr op in let a = app_op st op in
                        let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                                       (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && matched x d tr))) tr.l in
                        let enq_list1 = filter_op (fun x -> is_enqueue x && mem x ax.l && not
                                        (exists_mem ax.l (fun d -> is_dequeue d && mem d ax.l && mem x ax.l && matched x d ax))) ax.l in
                        let enq_list2 = filter_op (fun x -> is_enqueue x && mem x ax.l && not
                                        (exists_mem ax.l (fun d -> is_dequeue d && mem d ax.l && mem x ax.l && matched x d ax))) tr.l in
                        eff_enq0 tr op;
                        assert(forall_mem enq_list1 (fun x -> mem x ax.l && is_enqueue x && mem ((get_id x), (get_ele x)) (a.ls)));
                        assert(forall_mem (a.ls) (fun x -> mem ((fst x), Enqueue (snd x)) enq_list1)); ()
    | (id, Dequeue x) -> let ax = append tr op in let a = app_op st op in
                        let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                                       (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && matched x d tr))) tr.l in
                        let enq_list1 = filter_op (fun x -> is_enqueue x && mem x ax.l && not
                                        (exists_mem ax.l (fun d -> is_dequeue d && mem d ax.l && mem x ax.l && matched x d ax))) ax.l in
                        let enq_list2 = filter_op (fun x -> is_enqueue x && mem x ax.l && not
                                        (exists_mem ax.l (fun d -> is_dequeue d && mem d ax.l && mem x ax.l && matched x d ax))) tr.l in
                        eff_enq0 tr op;
                        // assert(forall_mem enq_list1 (fun x -> mem x ax.l && is_enqueue x && mem ((get_id x), (get_ele x)) (a.ls)));
                        // assert(forall_mem [op] (fun x -> mem x ax.l && is_enqueue x && mem ((get_id x), (get_ele x)) (a.ls)));
                        // assert(op::enq_list = enq_list1);
                        // assert(forall_mem (op::enq_list) (fun x -> mem x ax.l && is_enqueue x && mem ((get_id x), (get_ele x)) (a.ls)));
                        // assert(op::tr.l = ax.l);
                        // assert(forall e. mem e (op::enq_list) ==> mem e enq_list1);
                        // assert(mem op enq_list1);
                        // assert(sim0 ax a);
                        // assert(forall e. (mem e tr.l /\ (exists (d:o{ mem d tr.l }). matched e d tr)) ==> (mem e ax.l /\ (exists (d:o{ mem d ax.l }). matched e d ax)));
                        // assert(exists x. (mem x enq_list1 /\ not (mem (get_id x, get_ele x) a.ls)));
                        // assert(forall e. mem e enq_list1 ==> mem e enq_list \/ e = op);
                        // assert(forall_mem (a.ls) (fun x -> mem ((fst x), Enqueue (snd x)) enq_list));
                        // assert(forall_mem (a.ls) (fun x -> mem ((fst x), Enqueue (snd x)) enq_list1));
                         admit()


val prop_oper1: tr:ae
                -> st:s
                -> op:o
                -> Lemma (requires (sim1 tr st) /\ (not (member (get_id op) tr.l)))
                         (ensures (sim1 (append tr op) (app_op st op)))


