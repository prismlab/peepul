module Fqueue_new

open FStar.List.Tot
open Library_old
open FStar.All

#set-options "--query_stats"

type op =
  | Enqueue : nat -> op
  | Dequeue : (option nat) -> op
  | Rd

val is_enqueue : v:(nat * op) -> Tot (b:bool{(exists n. (get_op v = (Enqueue n))) <==> b = true})
let is_enqueue v = match v with
  | (_, Enqueue _) -> true
  | _ -> false

val is_dequeue : v:(nat * op) -> Tot (b:bool{(exists x. get_op v = Dequeue x) <==> b = true})
let is_dequeue v = match v with
  | (_, Dequeue _) -> true
  | _ -> false

val get_ele : e:(nat * op){is_enqueue e} -> Tot (n:nat{e = (get_id e, (Enqueue n))})
let get_ele (id, Enqueue x) = x

val return : d:(nat * op){is_dequeue d} -> Tot (v:option nat{d = (get_id d, (Dequeue v))})
let return (id, Dequeue x) = x

(* Return the position of a pair in a list of (nat * nat) pairs *)
val position : e:(nat * nat)
             -> s1:(list (nat * nat)) {mem e s1 /\ unique_id s1}
             -> Tot nat  (decreases (s1))
let rec position e s1 =
  match s1 with
  |x::xs -> if (e = x) then 0 else 1 + position e xs

(* Check if e1, different than e2, occurs before e2 in the list s1  *)
val order : e1:(nat * nat)
          -> e2:(nat * nat) {fst e1 <> fst e2}
          -> s1:list (nat * nat) {mem e1 s1 /\ mem e2 s1 /\ unique_id s1}
          -> Tot (r:bool {(position e1 s1 < position e2 s1) <==> r = true})
let order e1 e2 s1 = (position e1 s1 < position e2 s1)

val rev_acc : l: list (nat * nat) -> acc: list (nat * nat) -> Tot (ls:list (nat * nat){(forall e. mem e l \/ mem e acc <==> mem e ls)})
let rec rev_acc l acc =
  match l with
  | [] -> acc
  | hd :: tl -> rev_acc tl (hd :: acc)

val rev : l:list (nat * nat) -> Tot (rl:list (nat * nat){forall e. mem e l <==> mem e rl})
let rev l = rev_acc l []

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

val ax1 : l1:list (nat * nat){unique_id l1} -> l2:list (nat * nat){unique_id l2} 
        -> x:(nat * nat){not (mem_id (fst x) l1) /\ not (mem_id (fst x) l2)}
        -> Lemma (ensures (not (mem_id (fst x) (l1 @ l2))))
let rec ax1 l1 l2 x = match l1 with
  | [] -> ()
  | y::ys -> ax1 ys l2 x

val app_uni : l:list (nat * nat){unique_id l} 
            -> x:(nat * nat){not (mem_id (fst x) l)}
            -> Lemma (ensures (unique_id (l @ [x])))  
            [SMTPat (unique_id (l @ [x]))]
let rec app_uni l x = match l with
  | [] -> ()
  | y::ys -> app_uni ys x; ax1 ys [x] y

val rev2 : l:list (nat * nat){unique_id l} ->
         Lemma (ensures (l = [] \/ (rev l = ((rev (tl l)) @ [(hd l)]))))
let rec rev2 l = match l with
  | [] -> ()
  | x::xs -> rev2 xs; rev_app l;
         assert(xs = [] \/ rev xs = ((rev (tl xs)) @ [(hd xs)]))

val rev_unique : l:list (nat * nat){unique_id l} -> Lemma (ensures (unique_id (rev l))) [SMTPat (rev l)]
let rec rev_unique l = match l with
  | [] -> ()
  | x::xs -> rev_unique xs; app_uni (rev xs) x; rev2 l

val rev_unique1 : l:list (nat * nat){unique_id l} -> Lemma (ensures (unique_id l <==> unique_id (rev l))) [SMTPat (rev l)]
let rev_unique1 l = match l with
  | [] -> ()
  | x::xs -> rev_unique l

val app_length : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} -> Lemma (ensures (length l + 1 = length (l @ [x])))
let rec app_length l x = match l with
  | [] -> ()
  | y::ys -> app_length ys x

val rev_length0 : l:list (nat * nat){unique_id l} -> Lemma (ensures (length l = length (rev l))) [SMTPat (rev l)]
let rec rev_length0 l = match l with
  | [] -> ()
  | x::xs -> rev_length0 xs; rev_cor xs; rev_cor l; app_length xs x; rev2 l

val mem_app : l:list (nat * nat){unique_id l}
                -> e: (nat * nat){not(mem_id (fst e) l)}
                -> Lemma (ensures (forall x. mem x l \/ x = e <==> mem x (l @ [e]))) (decreases (l)) [SMTPat (mem e (l @ [e]))]
let rec mem_app l e = match l with
  | [] -> ()
  | y::ys -> mem_app ys e

val rev_length2 : l:list (nat * nat){unique_id l}
                -> e: (nat * nat){not(mem_id (fst e) l)}
                -> Lemma (ensures (forall x. mem x l ==> mem x (l @ [e]) /\ position x l = position x (l @ [e]))) (decreases (l))
let rec rev_length2 l e = match l with
  | [] -> ()
  | x::xs -> rev_length2 xs e

val rev_length4 : l:list (nat * nat){unique_id l}
                -> e: (nat * nat){not(mem_id (fst e) l)}
                -> Lemma (ensures ((length l = (position e (l @ [e])))))
let rec rev_length4 l e = match l with
  | [] -> ()
  | x::xs -> rev_length4 xs e

val rev_length3 : l:list (nat * nat){unique_id l} 
                -> Lemma (ensures (l <> [] ==> (length l - 1 = (position (hd l) (rev l)))))
let rec rev_length3 l = match l with
  | [] -> ()
  | x::[] -> ()
  | x::xs -> rev_length3 xs; rev2 l; rev_length4 (rev xs) x

val rev_length1 : l:list (nat * nat){unique_id l} 
                -> Lemma (ensures (forall e. mem e l ==> (length l - position e l - 1 = (position e (rev l)))))
let rec rev_length1 l = match l with
  | [] -> ()
  | x::xs -> rev_length1 xs; rev_length0 xs; rev_length0 l; rev2 l; mem_app (rev xs) x; rev_length2 (rev xs) x; rev_length3 l

val rev_ord : l:list (nat * nat){unique_id l} 
            -> Lemma (ensures (forall e e1. mem e l /\ mem e1 l /\ fst e <> fst e1 /\ order e e1 l <==>
                             mem e (rev l) /\ mem e1 (rev l) /\ fst e <> fst e1 /\ order e1 e (rev l))) [SMTPat (rev l)]
let rev_ord l = match l with
  | [] -> ()
  | x::xs -> rev_length1 l

type s =
    |S : front : list (nat (* UID *) * nat (* value of the element *)) {unique_id front}
       -> back  : list (nat (* UID *) * nat (* value of the element *)) {unique_id back /\
                                                              (forall e. mem e front ==> not (mem_id (fst e) back)) /\
                                                              (forall e. mem e back ==> not (mem_id (fst e) front))}
       -> s

type rval = 
  |Val : s -> rval
  |Ret : option nat -> rval
  |Bot

val memq : n:(nat * nat) -> q:s -> Tot (b:bool{b = true <==> (mem n q.front \/ mem n q.back)})
let memq n q = (mem n q.front || mem n q.back)

val app : l1:(list (nat * nat))
        -> l2:(list (nat * nat))
        -> Pure (list (nat * nat))
               (requires (unique_id l1 /\ unique_id l2) /\ (forall e. mem e l1 ==> not (mem_id (fst e) l2)))
               (ensures (fun r -> (forall e. mem e r <==> mem e l1 \/ mem e l2) /\ unique_id r /\
                               (forall e e1. (mem e l1 /\ mem e1 l1 /\ fst e <> fst e1 /\ order e e1 l1) \/
                                        (mem e l2 /\ mem e1 l2 /\ fst e <> fst e1 /\ order e e1 l2) \/
                                        (mem e l1 /\ mem e1 l2 /\ fst e <> fst e1) <==> mem e r /\ mem e1 r /\ fst e <> fst e1 /\ order e e1 r) /\ length r = length l1 + length l2))
                 (decreases %[l1;l2])
let rec app l1 l2 =
  match l1,l2 with
  |[], [] -> []
  |x::xs, [] -> x::xs
  |x::xs, _ -> x::(app xs l2)
  |[], x::xs -> x::xs

#set-options "--initial_fuel 10 --ifuel 10 --initial_ifuel 10 --fuel 10 --z3rlimit 100000"

val tolist : s1:s
           -> Pure (list (nat * nat))
                  (requires true)
                  (ensures (fun r -> (forall e. mem e r <==> memq e s1) /\ unique_id r /\
                           (forall e e1. (mem e s1.front /\ mem e1 s1.front /\ fst e <> fst e1 /\ order e e1 s1.front) \/
                                    (mem e s1.back /\ mem e1 s1.back /\ fst e <> fst e1 /\ order e e1 (rev s1.back)) \/
                                    (mem e s1.front /\ mem e1 s1.back /\ fst e <> fst e1) <==> mem e r /\ mem e1 r /\ fst e <> fst e1 /\  order e e1 r) /\ length r = length s1.front + length s1.back))
let tolist (S f b) = app f (rev b)

val norm : s0:s -> Tot (s1:s{((forall e e1. (memq e s1 /\ memq e1 s1 /\ fst e <> fst e1 /\ order e e1 (tolist s1)) <==>
                              (memq e s0 /\ memq e1 s0 /\ fst e <> fst e1 /\ order e e1 (tolist s0))) /\ 
                              (forall e. memq e s1 <==> memq e s0) /\ length (tolist s0) = length (tolist s1))})
let norm q =
  match q with
  |(S [] back) -> (S (rev back) [])
  |_ -> q

val peek : s1:s
         -> Pure (option nat)
                (requires true)
                (ensures (fun r -> ((norm s1).front = [] ==> r = None) /\
                                ((norm s1).front <> [] ==> (exists id. r = Some (id)))))
let peek q =
  let n = norm q in
  match n with
  |(S [] []) -> None
  |(S (x::_) _) -> Some (get_id x)

val last_ele : l:(list (nat * nat)){l <> []} -> (nat * nat)
let rec last_ele l = match l with
  | x::[] -> x
  | x::xs -> last_ele xs

val rear : s1:s
         -> Pure (option (nat * nat))
                (requires true)
                (ensures (fun r -> (s1.front = [] /\ s1.back = []  ==> r = None) /\
                                (s1.back <> [] ==> (exists id n. r = Some (id,n))) /\
                                (s1.front <> [] /\ s1.back = [] ==> (exists x. r = Some (last_ele x)))))
let rear q =
  match q with
  |(S [] []) -> None
  |(S _ (x::_)) -> Some x
  |(S x []) -> Some (last_ele x)

val init:s
let init = S [] []

val empty_mem : l:list (nat * nat){unique_id l /\ l = []} -> Lemma (ensures (forall (x:(nat * nat)). not (mem_id (fst x) l)))
let empty_mem l = ()

val mem_sublist : l:list (nat * nat){unique_id l /\ Cons? l} 
                -> x:(nat * nat){not (mem_id (fst x) l)} 
                -> Lemma (ensures (not (mem_id (fst x) (tl l))))
let rec mem_sublist l x = match l with
  | x::[] -> empty_mem (tl l)
  | x::xs -> mem_sublist xs x

val mem_sl : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)}
           -> Lemma (ensures (Cons? l ==> (not (mem_id (fst x) (tl l))) /\ (l = [] ==> not (mem_id (fst x) l))))
let mem_sl l x = match l with
  | [] -> empty_mem l
  | l -> mem_sublist l x

val ax5 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)}
        ->  y:(nat * nat){(not (mem_id (fst y) l) /\ fst y <> fst x)} 
        -> Lemma (ensures (not (mem_id (fst y) (l @ [x]))))
let rec ax5 l x y = match l with
  | [] -> ()
  | z::zs -> ax5 zs x y

val ax3 : l1:list (nat * nat){unique_id l1} -> x:(nat * nat){not (mem_id (fst x) l1)} 
        -> Lemma (ensures (unique_id (l1 @ [x])))
let rec ax3 l1 x = match l1 with
  | [] -> ()
  | y::ys -> ax3 ys x; ax5 ys x y

val ax6 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)} 
        -> Lemma (ensures (forall e. ((mem e l \/ e = x) <==> mem e (l @ [x]))))
let rec ax6 l x = match l with
  | [] -> ()
  | y::ys -> if y = x then () else ax6 ys x

val ax7 : l:list (nat * nat) -> x:(nat * nat) 
        -> Lemma (ensures (last_ele (l @ [x]) = x))
let rec ax7 l x = match l with
  | [] -> ()
  | y::ys -> ax7 ys x

val ax9 : l:list (nat * nat){unique_id l} -> x:(nat * nat){not (mem_id (fst x) l)}
        -> Lemma (ensures (forall e. (mem e l ==> (mem e (l @ [x]) /\ (unique_id (l @ [x])) /\ 
                         (mem x (l @ [x])) /\ order e x (l @ [x])))))
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
             (requires (not (mem_id (fst x) s1.front) /\ not (mem_id (fst x) s1.back)))
             (ensures (fun r -> (rear r = Some x) /\ (forall e. memq e s1 \/ e = x <==> memq e r) /\
                      (forall e e1. mem e s1.front /\ mem e1 s1.front /\ fst e <> fst e1 /\ order e e1 s1.front ==> order e e1 (tolist r)) /\
                      (forall e e1. mem e s1.back /\ mem e1 s1.back /\ order e e1 s1.back /\ fst e <> fst e1 ==> order e e1 (rev (tolist r))) /\
                      (forall e e1. mem e s1.front /\ mem e1 s1.back /\ fst e <> fst e1 ==> order e e1 (tolist r)) /\
                      (forall e. memq e s1 ==> order e x (tolist r)) /\
                      (length (tolist s1) + 1 = length (tolist r))))

let enqueue x s1 = (S s1.front (x::s1.back))

#set-options "--initial_fuel 7 --ifuel 7 --initial_ifuel 7 --fuel 7 --z3rlimit 10000"

val enqueue01 :x:(nat * nat)
             -> s1:s
             -> Lemma (requires (not (mem_id (fst x) s1.front) /\ not (mem_id (fst x) s1.back) /\ (s1.front = [] /\ s1.back <> [])))
                     (ensures (forall e e1. (memq e s1 /\ fst e <> fst e1 /\ ((memq e1 s1 /\ order e e1 (tolist s1)) \/ (e1 = x))) <==>
                       (memq e (enqueue x s1) /\ memq e1 (enqueue x s1) /\ fst e <> fst e1 /\ order e e1 (tolist (enqueue x s1)))))
                       (decreases (length (tolist (s1))))  [SMTPat (enqueue x s1)]

let enqueue01 x s1 = ()

val enqueue0 :x:(nat * nat)
             -> s1:s
             -> Lemma (requires (not (mem_id (fst x) s1.front) /\ not (mem_id (fst x) s1.back)))
                     (ensures (forall e e1. (memq e s1 /\ fst e <> fst e1 /\ ((memq e1 s1 /\ order e e1 (tolist s1)) \/ (e1 = x))) <==>
                       (memq e (enqueue x s1) /\ memq e1 (enqueue x s1) /\ fst e <> fst e1 /\ order e e1 (tolist (enqueue x s1)))))
                       (decreases (length (tolist (s1))))  [SMTPat (enqueue x s1)]


let rec enqueue0 x s1 = match (s1) with
  | S [] [] -> ()
  | S (y::ys) [] -> enqueue0 x (S ys [])
  | S (y::ys) (g::gs) -> enqueue0 x (S ys (g::gs))
  | S [] (g::gs) -> if (tl (rev (g::gs)) = []) then () else
                  enqueue01 x s1

val get_val : a:option nat{Some? a} -> n:(nat){a = Some n}
let get_val a = match a with
    | Some x -> x

val is_empty : s1:s -> Tot (b:bool{(s1.front = [] /\ s1.back = []) <==> b = true})
let is_empty s = (s.front = [] && s.back = [])

val dequeue : s1:s
            -> Pure ((option nat) * s)
              (requires true)
              (ensures (fun (v, r) -> (forall e. memq e r <==> memq e s1 /\ Some (get_id e) <> peek s1) /\
                          (forall e e1. mem e r.front /\ mem e1 r.front /\ fst e <> fst e1 /\ order e e1 r.front ==> order e e1 (tolist s1)) /\
                          (forall e e1. mem e r.back /\ mem e1 r.back /\ fst e <> fst e1 /\ order e e1 r.back ==> order e e1 (rev (tolist s1))) /\
                          (forall e e1. mem e r.front /\ mem e1 (rev r.back) /\ fst e <> fst e1 ==> order e e1 (tolist s1)) /\
                              ((is_empty s1) ==> ((forall e e1. (memq e r /\ memq e1 r /\ fst e <> fst e1 /\ order e e1 (tolist r)) <==>
                                         (memq e s1 /\ memq e1 s1 /\ fst e <> fst e1 /\  order e e1 (tolist s1))))) /\
                              ((is_empty s1) <==> (is_empty r /\ v = None))
                          ))

let dequeue q =
  match q with
  |(S [] []) -> (None, q)
  |(S (x::xs) _) -> (Some (get_id x), (S xs q.back))
  |(S [] (x::xs)) -> let (S (y::ys) []) = norm q in
                   (Some (get_id y), (S ys []))

val get_st : #s:eqtype ->  #rval:eqtype -> (s * rval) -> s
let get_st (s,r) = s

val get_rval : #s:eqtype ->  #rval:eqtype -> (s * rval) -> rval
let get_rval (s,r) = r

val app_op : s1:s
           -> op:(nat * op)
           -> Pure (s * rval)
             (requires ((not (mem_id (get_id op) s1.front)) /\ (not (mem_id (get_id op) s1.back))))
             (ensures (fun r ->
                           (is_enqueue op ==> ((rear (get_st r) = Some (get_id op, get_ele op)) /\ (forall e. memq e s1 \/ e = (get_id op, get_ele op) <==> memq e (get_st r)) /\
                                                   (forall e e1. mem e s1.front /\ mem e1 s1.front /\ fst e <> fst e1 /\ order e e1 s1.front ==> order e e1 (tolist (get_st r))) /\
                                                   (forall e e1. mem e s1.back /\ mem e1 s1.back /\ fst e <> fst e1 /\ order e e1 s1.back ==> order e e1 (rev (tolist (get_st r)))) /\
                                                   (forall e e1. mem e s1.front /\ mem e1 s1.back /\ fst e <> fst e1 ==> order e e1 (tolist (get_st r))) /\
                                                 (forall e e1. (mem e (tolist s1) /\ fst e <> fst e1 /\ ((mem e1 (tolist s1) /\ order e e1 (tolist s1)) \/
                                                   (e1 = (get_id op, get_ele op)))) <==>
                                                       (mem e (tolist (get_st r)) /\ mem e1 (tolist (get_st r)) /\ fst e <> fst e1 /\ order e e1 (tolist (get_st r)))) /\
                                                   (forall e. memq e s1 ==> order e (get_id op, get_ele op) (tolist (get_st r))))) /\
                           (is_dequeue op ==> ((forall e. memq e (get_st r) <==> memq e s1 /\ Some (get_id e) <> peek s1) /\
                                                (forall e e1. mem e (get_st r).front /\ mem e1 (get_st r).front /\ fst e <> fst e1 /\ order e e1 (get_st r).front ==> order e e1 (tolist s1)) /\
                                                (forall e e1. mem e (get_st r).back /\ mem e1 (get_st r).back /\ fst e <> fst e1 /\ order e e1 (get_st r).back ==> order e e1 (rev (tolist s1))) /\
                                            (forall e e1. mem e (get_st r).front /\ mem e1 (rev (get_st r).back) /\ fst e <> fst e1 ==> order e e1 (tolist s1)) /\
                                              (not (is_empty s1) ==> (((peek s1) <> None) /\ (forall e e1. (memq e (get_st r) /\ memq e1 (get_st r) /\ fst e <> fst e1 /\ order e e1 (tolist (get_st r))) <==>
                                             (memq e s1 /\ memq e1 s1 /\ fst e <> fst e1 /\ (get_id e) <> get_val (peek s1) /\ (get_id e1) <> get_val (peek s1) /\ order e e1 (tolist s1))))) /\
                                             ((is_empty s1) ==> ((forall e e1. (memq e (get_st r) /\ memq e1 (get_st r) /\ fst e <> fst e1 /\ order e e1 (tolist (get_st r))) <==>
                                                   (memq e s1 /\ memq e1 s1 /\ fst e <> fst e1 /\  order e e1 (tolist s1))))) /\
                                          ((is_empty s1) <==> (is_empty (get_st r) /\ (peek s1) = None)))) /\
                           (exists n. get_op op = (Enqueue n) ==> (exists id. rear (get_st r) = (Some (id,n)))) /\
                           (not (is_empty s1) /\ is_dequeue op ==> not (mem_id (get_val (peek s1)) (tolist (get_st r)))) /\
                           ((is_empty s1) /\ is_dequeue op ==> (is_empty (get_st r)))
                      ))

let app_op s e =
  match e with
  | (id, Enqueue n) -> (enqueue (id,n) s, Bot)
  | (_, Dequeue x) -> (snd (dequeue s), Ret x)
  | (_, Rd) -> (s, Val s)

val matched : e:(nat * op) -> d:(nat * op) -> tr:ae op
            -> Pure bool (requires (get_id e <> get_id d))
                        (ensures (fun b -> (is_enqueue e /\ is_dequeue d /\ mem e tr.l /\ mem d tr.l /\ return d = Some (get_id e) /\ (tr.vis e d)) <==> (b = true)))
let matched e d tr = (is_enqueue e && is_dequeue d && mem e tr.l && mem d tr.l && return d = Some (get_id e)) && (tr.vis e d)

val sub_list : e:(nat * op) 
             -> l:list (nat * op){mem e l /\ unique_id l} 
             -> l1:list (nat * op){not (mem e l1) /\ unique_id l1 /\ (forall e. mem e l1 ==> mem e l) /\ length l1 <= length l}
let rec sub_list e l = match l with
  | x::xs -> if x = e then xs else sub_list e xs

val position_o : e:(nat * op)
               -> s1:(list (nat * op)) {mem e s1 /\ unique_id s1}
               -> Tot nat  (decreases (s1))
let rec position_o e s1 =
  match s1 with
  |x::xs -> if (e = x) then 0 else 1 + (position_o e xs)

val ord : e1:(nat * op)
        -> e2:(nat * op){(fst e1) <> (fst e2)}
        -> s1:(list (nat * op)) {mem e1 s1 /\ mem e2 s1 /\ unique_id s1}
        -> Tot (r:bool {(position_o e1 s1 < position_o e2 s1) <==> r = true})
let ord e1 e2 s1 = (position_o e1 s1 < position_o e2 s1)

val ob : e:(nat * op) -> d:(nat * op){fst e <> fst d} 
       -> l:list (nat * op){mem e l /\ mem d l /\ unique_id l} -> Tot (b:bool{ord e d l <==> b = true})
let rec ob e d l = match l with
  | x::xs -> if x = e then mem d xs else
           (if x <> d then ob e d xs else false)

val max : x:int -> y:int -> Tot (z:int{z >= x /\ z >= y})
let max x y = if x > y then x else y

val len_del : l:list (nat * op){unique_id l} -> Tot int
let rec len_del l = match l with
  | [] -> 0
  | x::xs -> if (is_enqueue x) then 1 + (len_del xs) else ((-1) + len_del xs)

val is_empty' : l:list (nat * op){unique_id l} -> s1:s -> Tot bool
let is_empty' l s1 = ((length s1.front + length s1.back) + (len_del l) = 0)

val filter_s : f:((nat * nat) -> bool)
             -> l:list (nat * nat) {unique_id l}
             -> Tot (l1:list (nat * nat) {(forall e. mem e l1 <==> mem e l /\ f e) /\ unique_id l1}) (decreases l)
let rec filter_s f l =
    match l with
    | [] -> []
    | hd::tl -> if f hd then hd::(filter_s f tl) else filter_s f tl

val filter_op : f:((nat * op) -> bool)
              -> l:list (nat * op)
              -> Tot (l1:list (nat * op) {(forall e. mem e l1 <==> (mem e l /\ f e))})
let rec filter_op f l =
  match l with
  | [] -> []
  | hd::tl -> if f hd then hd::(filter_op f tl) else filter_op f tl

val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat)
               -> Lemma (requires (unique_id l))
                       (ensures (unique_id (filter_s f l)) /\ (forall e. mem e (filter_s f l) <==> mem e l /\ f e) /\
                                (forall e e1. fst e <> fst e1 /\ mem e (filter_s f l) /\ mem e1 (filter_s f l) /\ order e e1 (filter_s f l) <==>
                                           mem e l /\ mem e1 l  /\ order e e1 l /\ f e /\ f e1))
                       [SMTPat (filter_s f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val sorted : list(nat * nat) -> bool
let rec sorted l = match l with
  |[] |[_] -> true
  |x::xs -> forallb (fun (e:nat*nat) -> fst x < fst e) xs && sorted xs

val test_sorted: x:(nat * nat) -> l:list (nat * nat) ->
      Lemma ((sorted (x::l) /\ Cons? l) ==> fst x < fst (Cons?.hd l))
let test_sorted x l = ()

val test_sorted2: unit -> Tot (m:list (nat * nat){sorted m})
let test_sorted2 () = Nil

val sorted_smaller : x:(nat * nat)
                   ->  y:(nat * nat)
                   ->  l:list (nat * nat)
                   ->  Lemma (requires (sorted (x::l) /\ mem y l))
                            (ensures (fst x < fst y))
                            [SMTPat (sorted (x::l)); SMTPat (mem y l)]
let rec sorted_smaller x y l = match l with
  | [] -> ()
  | z::zs -> if z=y then () else sorted_smaller x y zs

type permutation (l1:list (nat * nat)) (l2:list (nat * nat)) =
    length l1 = length l2 /\ (forall n. mem n l1 = mem n l2)

type permutation_2 (l:list (nat * nat)) (l1:list (nat * nat)) (l2:list (nat * nat)) =
    (forall n. mem n l = (mem n l1 || mem n l2)) /\
    length l = length l1 + length l2

type split_inv (l:list (nat * nat)) (l1:list (nat * nat)) (l2:list (nat * nat)) =
    permutation_2 l l1 l2 /\ length l > length l1 /\ length l > length l2

val filter_sort : f:((nat * nat) -> bool)
               -> l:list (nat * nat)
               -> Lemma (requires (unique_id l /\ sorted l))
                       (ensures (sorted (filter_s f l)) /\ (forall e. mem e (filter_s f l) <==> mem e l /\ f e) /\
                                (forall e e1. fst e <> fst e1 /\ mem e (filter_s f l) /\ mem e1 (filter_s f l) /\ order e e1 (filter_s f l) <==>
                                           mem e l /\ mem e1 l  /\ order e e1 l /\ f e /\ f e1))
                       [SMTPat (filter_s f l)]

let rec filter_sort f l =
  match l with
  | [] -> ()
  | x::xs -> filter_sort f xs

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

#push-options "--initial_fuel 10 --ifuel 10 --initial_ifuel 10 --fuel 10 --z3rlimit 10000000000"

val sim0 : tr:ae op
         -> s0:s
         -> Tot(b:bool{b = true <==> (forall e. memq e s0 <==> (mem (fst e, Enqueue (snd e)) tr.l /\
             (forall d. mem d tr.l /\ fst e <> get_id d /\ is_dequeue d ==> (not (matched (fst e, Enqueue (snd e)) d tr)))))})

let sim0 tr s0 =
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && get_id x <> get_id d && matched x d tr))) tr.l in
  if forall_mem enq_list (fun x -> mem x tr.l && is_enqueue x && mem ((get_id x), (get_ele x)) (tolist s0)) &&
       forall_mem (tolist s0) (fun x -> mem ((fst x), Enqueue (snd x)) enq_list)
                            then true else false

val sim1 : tr:ae op
         -> s0:s
         -> Tot (b:bool {b = true <==> (forall e e1. (memq e s0 /\ memq e1 s0 /\ fst e <> fst e1 /\ order e e1 (tolist s0) ==>
                                      (mem (fst e, Enqueue (snd e)) tr.l /\ mem (fst e1, Enqueue (snd e1)) tr.l /\ fst e <> fst e1 /\
                                           (forall d. mem d tr.l /\ is_dequeue d /\ fst e <> get_id d ==> not (matched (fst e, Enqueue (snd e)) d tr)) /\
                                           (forall d. mem d tr.l /\ is_dequeue d /\ fst e1 <> get_id d ==> not (matched (fst e1, Enqueue (snd e1)) d tr)) /\
                                      ((tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                               (not (tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                                    tr.vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                      (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1))))))))})

#set-options "--z3rlimit 10000"
let sim1 tr s0 =
  let enq_list = filter_op (fun (x:(nat * op)) -> is_enqueue x && mem x tr.l && not
                               (exists_mem tr.l (fun (d:(nat * op)) -> is_dequeue d && mem d tr.l && get_id x <> get_id d && matched x d tr))) tr.l in
        (forall_mem (tolist s0) (fun (e:(nat * nat)) -> (forall_mem (filter_s (fun (e1:(nat * nat)) -> memq e s0 && memq e1 s0 && fst e <> fst e1 && order e e1 (tolist s0)) (tolist s0))
                    (fun (e1:(nat * nat)) -> (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       ((tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not (tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                tr.vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                       (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1))))))))))

val sim2 : tr:ae op
        -> s0:s
        -> Tot (b:bool {b = true <==> (forall e e1. ((mem (fst e, Enqueue (snd e)) tr.l /\ mem (fst e1, Enqueue (snd e1)) tr.l /\ fst e <> fst e1 /\
                                       (forall d. mem d tr.l /\ is_dequeue d /\ fst e <> get_id d ==> not (matched (fst e, Enqueue (snd e)) d tr)) /\
                                       (forall d. mem d tr.l /\ is_dequeue d /\ fst e1 <> get_id d ==> not (matched (fst e1, Enqueue (snd e1)) d tr)) /\
                                    ((tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                             (not (tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                                  tr.vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                             (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))) ==>
                       memq e s0 /\ memq e1 s0 /\ fst e <> fst e1 /\ order e e1 (tolist s0)))})
#set-options "--z3rlimit 10000"
let sim2 tr s0 =
   let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                                (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && get_id x <> get_id d && matched x d tr))) tr.l in
                   (forall_mem (enq_list) (fun e -> is_enqueue e && (forall_mem (filter_op (fun e1 -> is_enqueue e1 && get_id e <> get_id e1 && ((tr.vis e e1) ||
                               (not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list))
                          (fun e1 -> is_enqueue e1 && memq ((get_id e), (get_ele e)) s0 && memq ((get_id e1), (get_ele e1)) s0 && get_id e <> get_id e1 &&
                             order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)))))

val sim : tr:ae op
        -> s0:s
        -> Tot(b:bool{b = true <==>
                       ((forall e. memq e s0 <==> (mem (fst e, Enqueue (snd e)) tr.l /\
                               (forall d. mem d tr.l /\ fst e <> get_id d /\ is_dequeue d ==> (not (matched (fst e, Enqueue (snd e)) d tr))))) /\
                                   (forall e e1. (memq e s0 /\ memq e1 s0 /\ fst e <> fst e1 /\ order e e1 (tolist s0) <==>
                                      (mem (fst e, Enqueue (snd e)) tr.l /\ mem (fst e1, Enqueue (snd e1)) tr.l /\ fst e <> fst e1 /\
                                           (forall d. mem d tr.l /\ is_dequeue d /\ fst e <> get_id d ==> not (matched (fst e, Enqueue (snd e)) d tr)) /\
                                           (forall d. mem d tr.l /\ is_dequeue d /\ fst e1 <> get_id d ==> not (matched (fst e1, Enqueue (snd e1)) d tr)) /\
                                      ((tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                               (not (tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                                    tr.vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                      (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))))))})

let sim tr s0 = sim0 tr s0 && sim1 tr s0 && sim2 tr s0

val extract : r:rval{Val? r} -> s
let extract (Val s) = s

val spec : o:(nat * op) -> tr:ae op
         -> Tot (r:rval{Rd? (get_op o) ==> Val? r /\ (let s0 = extract r in ((forall e. memq e s0 <==> (mem (fst e, Enqueue (snd e)) tr.l /\
                               (forall d. mem d tr.l /\ fst e <> get_id d /\ is_dequeue d ==> (not (matched (fst e, Enqueue (snd e)) d tr))))) /\
                                   (forall e e1. (memq e s0 /\ memq e1 s0 /\ fst e <> fst e1 /\ order e e1 (tolist s0) <==>
                                      (mem (fst e, Enqueue (snd e)) tr.l /\ mem (fst e1, Enqueue (snd e1)) tr.l /\ fst e <> fst e1 /\
                                           (forall d. mem d tr.l /\ is_dequeue d /\ fst e <> get_id d ==> not (matched (fst e, Enqueue (snd e)) d tr)) /\
                                           (forall d. mem d tr.l /\ is_dequeue d /\ fst e1 <> get_id d ==> not (matched (fst e1, Enqueue (snd e1)) d tr)) /\
                                      ((tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                               (not (tr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                                    tr.vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                      (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1))))))))))})
let spec o tr =
  match o with
  |(_, Enqueue _) -> Bot
  |(_, Dequeue x) -> Ret x
  |(_, Rd) -> admit()

val diff_s : a:list (nat * nat)
           -> l:list (nat * nat)
           -> Pure (list (nat * nat))
             (requires (unique_id a /\ unique_id l /\ sorted l /\ sorted a /\ (forall e e1. (mem e a /\ mem e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. mem e l /\ mem e1 l /\ mem e a /\ mem e1 a /\ order e e1 l ==> order e e1 a) /\
                              (forall e e1. mem e l /\ mem e1 a /\ not (mem e1 l) ==> (fst e) < (fst e1))))
             (ensures (fun d -> (forall e. mem e d <==> (mem e a /\ not (mem e l))) /\ unique_id d /\ sorted d /\ (forall e. mem_id e d <==> (mem_id e a /\ not (mem_id e l))) /\
                             (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ not (mem e l) /\ not (mem e1 l) /\ order e e1 a <==> mem e d /\ mem e1 d /\ order e e1 d)))
             (decreases %[a;l])

#set-options "--z3rlimit 1000"
let diff_s a l =
  filter_s (fun e -> not (mem e l)) a

val intersection : l:list (nat * nat)
                 -> a:list (nat * nat)
                 -> b:list (nat * nat)
                 -> Pure (list (nat * nat))
                    (requires unique_id l /\ unique_id a /\  unique_id b /\ sorted l /\ sorted a /\ sorted b /\
                              (forall e e1. (mem e a /\ mem e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. (mem e b /\ mem e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. mem e l /\ mem e1 l /\ mem e a /\ mem e1 a /\ order e e1 l ==> order e e1 a) /\
                              (forall e e1. mem e l /\ mem e1 l /\ mem e b /\ mem e1 b /\ order e e1 l ==> order e e1 b) /\
                              (forall e e1. mem e l /\ mem e1 a /\ not (mem e1 l) ==> (fst e) < (fst e1)) /\
                              (forall e e1. mem e l /\ mem e1 b /\ not (mem e1 l) ==> (fst e) < (fst e1)) /\
                              (forall e. mem e (diff_s a l) ==> not (mem_id (fst e) (diff_s b l))) /\
                              (forall e. mem e (diff_s b l) ==> not (mem_id (fst e) (diff_s a l))))
                    (ensures (fun i -> (forall e. mem e i <==> mem e a /\ mem e b /\ mem e l) /\ unique_id i /\ sorted i /\
                                    (forall e. mem_id e i <==> mem_id e l /\ mem_id e a /\ mem_id e b) /\
                                    (forall e e1. (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ order e e1 l /\
                                      mem e a /\ mem e1 a /\ order e e1 a /\ mem e b /\ mem e1 b /\ order e e1 b) <==> (mem e i /\ mem e1 i /\ order e e1 i))))

#set-options "--z3rlimit  1000"
let intersection l a b =
  filter_s (fun e -> mem e a && mem e b) l

val union_s : a:list (nat * nat)
            -> b:list (nat * nat)
            -> Pure (list (nat * nat))
              (requires unique_id a /\ unique_id b /\ (forall e. mem e a ==> not (mem_id (fst e) b)) /\ (forall e. mem e b ==> not (mem_id (fst e) a)) /\
                        (forall e e1. mem e a /\ mem e1 b ==> fst e < fst e1) /\ sorted a /\ sorted b)
              (ensures (fun u -> (forall e. mem e u <==> mem e a \/ mem e b) /\ unique_id u /\ sorted u /\
                              (forall e e1. ((mem e a /\ mem e1 a /\ fst e <> fst e1 /\ order e e1 a) \/ (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ order e e1 b) \/
                                             (mem e a /\ mem e1 b /\ fst e <> fst e1)) <==> (mem e u /\ mem e1 u /\ order e e1 u)))) (decreases (length a))

let rec union_s a b =
  match a,b with
    | [], [] -> []
    | x::xs, [] -> x::xs
    | [], x::xs -> x::xs
    | x::xs, y::ys -> assert(forall e. mem e a ==> fst e < fst y); (x::(union_s xs b))

val split: l:list (nat * nat){unique_id l} -> Pure (list (nat * nat) * list (nat * nat))
             (requires (Cons? l /\ Cons? (Cons?.tl l)))
	     (ensures (fun r -> unique_id (fst r) /\ unique_id (snd r) /\ split_inv l (fst r) (snd r) /\
                               (forall e. mem e (fst r) ==> not (mem_id (fst e) (snd r))) /\ (forall e. mem e (snd r) ==> not (mem_id (fst e) (fst r)))))
let rec split (x::y::l) =
  admit(); match l with
    | [] -> [x], [y]
    | [x'] -> x::[x'], [y]
    | _ -> let l1, l2 = split l in
           x::l1, y::l2

type merge_inv (l1:list (nat * nat)) (l2:list (nat * nat)) (l:list (nat * nat)) =
    (Cons? l1 /\ Cons? l /\ Cons?.hd l1 = Cons?.hd l) \/
    (Cons? l2 /\ Cons? l /\ Cons?.hd l2 = Cons?.hd l) \/
    (Nil? l1 /\ Nil? l2 /\ Nil? l)

val merge_sl: l1:list (nat * nat) -> l2:list (nat * nat) -> Pure (list (nat * nat))
             (requires (sorted l1 /\ sorted l2 /\ unique_id l1 /\ unique_id l2 /\
                               (forall e. mem e l1 ==> not (mem_id (fst e) l2)) /\ (forall e. mem e l2 ==> not (mem_id (fst e) l1))))
             (ensures (fun l -> unique_id l /\ sorted l /\ permutation_2 l l1 l2
                                         /\ merge_inv l1 l2 l))

let rec merge_sl l1 l2 = admit(); match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | h1::tl1, h2::tl2 -> if fst h1 < fst h2
                        then h1::(merge_sl tl1 l2)
                        else h2::(merge_sl l1 tl2)

val mergesort : l:list (nat * nat) {unique_id l}
              -> Pure (list (nat * nat)) (requires True)
                     (ensures (fun r -> unique_id r /\ sorted r /\ permutation l r)) (decreases (length l))
let rec mergesort l = match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let (l1, l2) = split l in
    let sl1 = mergesort l1 in
    let sl2 = mergesort l2 in
    merge_sl sl1 sl2

val sorted_list0 : l:list (nat * nat){unique_id l /\ sorted l} ->
                   Lemma (ensures ((forall x y. mem x l /\ mem y l /\ (fst x < fst y) <==> mem x l /\ mem y l /\ fst x <> fst y /\ order x y l))) [SMTPat (sorted l)]
let rec sorted_list0 l = match l with
  | [] -> ()
  | [x] -> ()
  | x::y::xs -> sorted_list0 (y::xs); assert(forall e. (mem e xs \/ e = y) ==> order x e l)

val sort : l:list (nat * nat) {unique_id l}
         -> Tot (m:list (nat * nat) {unique_id m /\ sorted m /\ permutation l m})
let sort l = mergesort l

val union1 : a:list (nat * nat)
           -> b:list (nat * nat)
           -> Pure (list (nat * nat))
               (requires (unique_id a /\ unique_id b) /\ (forall e. mem e a ==> not (mem_id (fst e) b)) /\ (forall e. mem e b ==> not (mem_id (fst e) a)) /\ sorted a /\ sorted b)
                 (ensures (fun u -> (forall e. mem e u <==> mem e a \/ mem e b) /\ unique_id u /\ sorted u /\
                               (forall e e1. ((mem e a /\ mem e1 a /\ fst e <> fst e1 /\ order e e1 a) \/
                               (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ order e e1 b)) ==> (mem e u /\ mem e1 u /\ order e e1 u))))

let rec union1 l1 l2 =
 match l1, l2 with
  | [], [] -> []
  | [], l2 -> l2
  | l1, [] -> l1
  | h1::t1, h2::t2 -> if (fst h1 < fst h2)
                   then h1::(union1 t1 l2) else h2::(union1 l1 t2)

val sorted_union : a:list (nat * nat)
                 -> b:list (nat * nat)
                 -> Pure (list (nat * nat))
                   (requires (unique_id a /\ unique_id b /\ sorted a /\ sorted b) /\ (forall e. mem e a ==> not (mem_id (fst e) b)) /\ (forall e. mem e b ==> not (mem_id (fst e) a)))
                   (ensures (fun u -> (forall e. mem e u <==> mem e a \/ mem e b) /\ unique_id u /\ sorted u /\
                               (forall e e1. ((mem e a /\ mem e1 a /\ fst e <> fst e1 /\ order e e1 a) \/
                               (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ order e e1 b)) ==> (mem e u /\ mem e1 u /\ order e e1 u))))

let sorted_union a b =
  union1 a b

val forallbq : f:((nat * nat) -> bool)
             -> l:s
             -> Tot (b:bool{(forall e. memq e l ==> f e) <==> b = true})

let forallbq f l =
  forallb (fun e -> f e) (tolist l)

val pre_cond_merge1_1 : l:s
                    -> a:s
                    -> b:s
                    -> Tot (b1:bool {b1 = true <==> 
                              unique_id (tolist l) /\ unique_id (tolist a) /\ unique_id (tolist b) /\ 
                              sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\
    (forall e e1. (mem e (tolist a) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
    (forall e e1. (mem e (tolist b) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
       (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
         (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1))})
let pre_cond_merge1_1 l a b =
    unique_id (tolist l) && unique_id (tolist a) && unique_id (tolist b) &&
    sorted (tolist l) && sorted (tolist a) && sorted (tolist b) &&
    forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e < fst e1) (filter_s (fun e -> not (mem e (tolist l))) (tolist a)))) (tolist l) &&
    forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e < fst e1) (filter_s (fun e -> not (mem e (tolist l))) (tolist b)))) (tolist l) &&
    forallbq (fun e -> (forallb (fun (e1:(nat * nat)) -> snd e = snd e1) (filter_s (fun e1 -> fst e = fst e1) (tolist l)))) a &&
    forallbq (fun e -> (forallb (fun (e1:(nat * nat)) -> snd e = snd e1) (filter_s (fun e1 -> fst e = fst e1) (tolist l)))) b

val pre_cond_merge1_2 : l:s
                    -> a:s
                    -> b:s
                    -> Tot (b1:bool {b1 = true <==> 
                              unique_id (tolist l) /\ unique_id (tolist a) /\ unique_id (tolist b) /\ 
                              sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\
    (forall e e1. (mem e (tolist a) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
    (forall e e1. (mem e (tolist b) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
       (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
         (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                  (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                    (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b))})

#set-options "--z3rlimit 10000"
let pre_cond_merge1_2 l a b = 
  pre_cond_merge1_1 l a b &&
    forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e (tolist a) && mem e1 (tolist a) && order e e1 (tolist a)) (filter (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e1 (tolist a) && mem e (tolist l) && mem e1 (tolist l) && order e e1 (tolist l)) (tolist l)))) (filter (fun (e:(nat * nat)) -> mem e (tolist a)) (tolist l)) &&
    forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e (tolist b) && mem e1 (tolist b) && order e e1 (tolist b)) (filter (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e1 (tolist b) && mem e (tolist l) && mem e1 (tolist l) && order e e1 (tolist l)) (tolist l)))) (filter (fun (e:(nat * nat)) -> mem e (tolist b)) (tolist l)) 
    
val pre_cond_merge1 : l:s
                    -> a:s
                    -> b:s
                    -> Tot (b1:bool {b1 = true <==> 
                              unique_id (tolist l) /\ unique_id (tolist a) /\ unique_id (tolist b) /\ 
                              sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\
    (forall e e1. (mem e (tolist a) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
    (forall e e1. (mem e (tolist b) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
       (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
         (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                  (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                    (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b)) /\
              (forall e. mem e (diff_s (tolist a) (tolist l)) ==> not (mem_id (fst e) (diff_s (tolist b) (tolist l)))) /\
              (forall e. mem e (diff_s (tolist b) (tolist l)) ==> not (mem_id (fst e) (diff_s (tolist a) (tolist l))))})

#set-options "--z3rlimit 10000"
let pre_cond_merge1 l a b = 
    pre_cond_merge1_1 l a b &&
    pre_cond_merge1_2 l a b &&
    forallb (fun (e:(nat * nat)) -> not (mem_id (get_id e) (diff_s (tolist b) (tolist l)))) (diff_s (tolist a) (tolist l)) &&
    forallb (fun (e:(nat * nat)) -> not (mem_id (get_id e) (diff_s (tolist a) (tolist l)))) (diff_s (tolist b) (tolist l))
    
val merge_s1 : l:list (nat * nat)
            -> a:list (nat * nat)
            -> b:list (nat * nat)
            -> Pure (list (nat * nat))
                   (requires unique_id a /\ unique_id l /\ unique_id b /\ sorted l /\ sorted a /\ sorted b /\
                              (forall e e1. (mem e a /\ mem e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. (mem e b /\ mem e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. mem e l /\ mem e1 a /\ not (mem e1 l) ==> (fst e) <= (fst e1)) /\
                              (forall e e1. mem e l /\ mem e1 b /\ not (mem e1 l) ==> (fst e) <= (fst e1)) /\
                              (forall e e1. mem e l /\ mem e1 l /\ mem e a /\ mem e1 a /\ order e e1 l ==> order e e1 a) /\
                              (forall e e1. mem e l /\ mem e1 l /\ mem e b /\ mem e1 b /\ order e e1 l ==> order e e1 b) /\
                              (forall e. mem e (diff_s a l) ==> not (mem_id (fst e) (diff_s b l))) /\
                              (forall e. mem e (diff_s b l) ==> not (mem_id (fst e) (diff_s a l))))
                   (ensures (fun res -> unique_id res /\ sorted res /\ (forall e. mem e res <==> ((mem e l /\ mem e a /\ mem e b) \/
                                    (mem e a /\ not (mem e l)) \/ (mem e b /\ not (mem e l)))) /\
                                    (forall e. mem e l /\ not (mem e a) ==> not (mem e res)) /\
                                    (forall e. mem e l /\ not (mem e b) ==> not (mem e res)) /\
                                    (forall e e1. ((mem e l /\ mem e1 l /\ fst e <> fst e1 /\ order e e1 l /\ mem e res /\ mem e1 res) \/
                                              (mem e a /\ mem e1 a /\ fst e <> fst e1 /\ order e e1 a /\ mem e res /\ mem e1 res) \/
                                              (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ order e e1 b /\ mem e res /\ mem e1 res) \/
                                              (mem e l /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ mem e res /\ mem e1 res) \/
                                              (mem e l /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ mem e res /\ mem e1 res) \/
                                              (((mem e (diff_s a l) /\ mem e1 (diff_s b l)) \/ (mem e1 (diff_s a l) /\ mem e (diff_s b l))) /\ (fst e < fst e1))) <==>
                                       (mem e res /\ mem e1 res /\ fst e <> fst e1 /\ order e e1 res))))

let merge_s1 l a b =
  let ixn = intersection l a b in
  let diff_a = diff_s a l in
  let diff_b = diff_s b l in
  let union_ab = sorted_union diff_a diff_b in
  let res = union_s ixn union_ab in
  assert(forall e. mem e res ==> (mem e ixn) \/ (mem e union_ab));
  assert(forall e. mem e a ==> mem e (diff_s a l) \/ mem e l);
  assert(forall e. mem e a /\ mem e res ==> mem e ixn \/ mem e (diff_s a l));
  assert(forall e e1. (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ order e e1 l /\ mem e res /\ mem e1 res) ==>
                                       (mem e res /\ mem e1 res /\ fst e <> fst e1 /\ order e e1 res));
  assert(forall e e1. ((mem e a /\ mem e1 a /\ fst e <> fst e1 /\ order e e1 a /\ mem e res /\ mem e1 res) \/
                  (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ order e e1 b /\ mem e res /\ mem e1 res) \/
                  (mem e l /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ mem e res /\ mem e1 res) \/
                  (mem e l /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ mem e res /\ mem e1 res) \/
                  (((mem e (diff_s a l) /\ mem e1 (diff_s b l)) \/ (mem e1 (diff_s a l) /\ mem e (diff_s b l))) /\ (fst e < fst e1))) ==>
                    (mem e res /\ mem e1 res /\ fst e <> fst e1 /\ order e e1 res));
  assert(forall e e1. ((mem e res /\ mem e1 res /\ fst e <> fst e1 /\ order e e1 res) ==>
                  (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ order e e1 l /\ mem e res /\ mem e1 res) \/
                  (mem e a /\ mem e1 a /\ fst e <> fst e1 /\ order e e1 a /\ mem e res /\ mem e1 res) \/
                  (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ order e e1 b /\ mem e res /\ mem e1 res) \/
                  (mem e l /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ mem e res /\ mem e1 res) \/
                  (mem e l /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ mem e res /\ mem e1 res) \/
                  (((mem e (diff_s a l) /\ mem e1 (diff_s b l)) \/ (mem e1 (diff_s a l) /\ mem e (diff_s b l))) /\ (fst e < fst e1))));
  res

#set-options "--z3rlimit 10000"
val merge_s : l:s -> a:s -> b:s 
            -> Pure s
              (requires (unique_id (tolist l) /\ unique_id (tolist a) /\ unique_id (tolist b) /\ 
                         sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\
                        (forall e e1. (mem e (tolist a) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                        (forall e e1. (mem e (tolist b) /\ mem e1 (tolist l) /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                        (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                        (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                        (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                        (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b)) /\
                        (forall e. mem e (diff_s (tolist a) (tolist l)) ==> not (mem_id (fst e) (diff_s (tolist b) (tolist l)))) /\
                        (forall e. mem e (diff_s (tolist b) (tolist l)) ==> not (mem_id (fst e) (diff_s (tolist a) (tolist l))))))
              (ensures (fun res -> unique_id res.front /\ sorted res.front /\ 
                (forall e. mem e res.front <==> ((mem e (tolist l) /\ mem e (tolist a) /\ mem e (tolist b)) \/
                (mem e (tolist a) /\ not (mem e (tolist l))) \/ (mem e (tolist b) /\ not (mem e (tolist l))))) /\
                (forall e. mem e (tolist res) <==> ((mem e (tolist l) /\ mem e (tolist a) /\ mem e (tolist b)) \/
                  (mem e (tolist a) /\ not (mem e (tolist l))) \/ (mem e (tolist b) /\ not (mem e (tolist l))))) /\
                (forall e. memq e res <==> ((memq e l /\ memq e a /\ memq e b) \/
                  (memq e a /\ not (memq e l)) \/ (memq e b /\ not (memq e l)))) /\
                (forall e. mem e (tolist l) /\ not (mem e (tolist a)) ==> not (mem e res.front)) /\
                (forall e. mem e (tolist l) /\ not (mem e (tolist b)) ==> not (mem e res.front)) /\
    (forall e e1. ((mem e (tolist l) /\ mem e1 (tolist l) /\ fst e <> fst e1 /\ order e e1 (tolist l) /\ mem e res.front /\ mem e1 res.front) \/
    (mem e (tolist a) /\ mem e1 (tolist a) /\ fst e <> fst e1 /\ order e e1 (tolist a) /\ mem e res.front /\ mem e1 res.front) \/
    (mem e (tolist b) /\ mem e1 (tolist b) /\ fst e <> fst e1 /\ order e e1 (tolist b) /\ mem e res.front /\ mem e1 res.front) \/
    (mem e (tolist l) /\ mem e1 (diff_s (tolist a) (tolist l)) /\ fst e <> fst e1 /\ mem e res.front /\ mem e1 res.front) \/
    (mem e (tolist l) /\ mem e1 (diff_s (tolist b) (tolist l)) /\ fst e <> fst e1 /\ mem e res.front /\ mem e1 res.front) \/
    (((mem e (diff_s (tolist a) (tolist l)) /\ mem e1 (diff_s (tolist b) (tolist l))) \/ (mem e1 (diff_s (tolist a) (tolist l)) /\ mem e (diff_s (tolist b) (tolist l)))) /\ (fst e < fst e1))) <==>
    (mem e res.front /\ mem e1 res.front /\ fst e <> fst e1 /\ order e e1 res.front))))

#set-options "--z3rlimit 10000"
let merge_s l a b =
  (S (merge_s1 (tolist l) (tolist a) (tolist b)) [])

val pre_cond_merge_1 : ltr:ae op
                   -> l:s
                   -> atr:ae op
                   -> a:s
                   -> btr:ae op
                   -> b:s
                   -> Tot (b1:bool {(b1 = true) <==> 
                              (sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\ 
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. (memq e a /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. (memq e b /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)))})

#set-options "--z3rlimit 10000"
let pre_cond_merge_1 ltr l atr a btr b = 
  sorted (tolist l) && sorted (tolist a) && sorted (tolist b) &&
  forallb (fun e -> not (mem_id (get_id e) atr.l)) ltr.l &&
  forallb (fun e -> not (mem_id (get_id e) btr.l)) ltr.l &&
  forallb (fun e -> not (mem_id (get_id e) btr.l)) atr.l &&
  forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e < fst e1) (filter_s (fun (e1:(nat * nat)) -> not (mem e1 (tolist l))) (tolist a)))) (tolist l) &&
  forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e < fst e1) (filter_s (fun (e1:(nat * nat)) -> not (mem e1 (tolist l))) (tolist b)))) (tolist l) &&
  forallbq (fun e -> (forallb (fun e1 -> snd e = snd e1) (filter (fun e1 -> fst e = fst e1) (tolist l)))) a &&
  forallbq (fun e -> (forallb (fun e1 -> snd e = snd e1) (filter (fun e1 -> fst e = fst e1) (tolist l)))) b 

#set-options "--z3rlimit 10000"
val pre_cond_merge_3 : ltr:ae op
                   -> l:s
                   -> atr:ae op
                   -> a:s
                   -> btr:ae op
                   -> b:s
                   -> Tot (b1:bool {(b1 = true) <==> 
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b))})

#set-options "--z3rlimit 10000"
let pre_cond_merge_3 ltr l atr a btr b = 
  forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e (tolist a) && mem e1 (tolist a) && order e e1 (tolist a)) (filter (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e1 (tolist a) && mem e (tolist l) && mem e1 (tolist l) && order e e1 (tolist l)) (tolist l)))) (filter (fun (e:(nat * nat)) -> mem e (tolist a)) (tolist l)) &&
  forallb (fun (e:(nat * nat)) -> (forallb (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e (tolist b) && mem e1 (tolist b) && order e e1 (tolist b)) (filter (fun (e1:(nat * nat)) -> fst e <> fst e1 && mem e1 (tolist b) && mem e (tolist l) && mem e1 (tolist l) && order e e1 (tolist l)) (tolist l)))) (filter (fun (e:(nat * nat)) -> mem e (tolist b)) (tolist l))
  
val pre_cond_merge : ltr:ae op
                   -> l:s
                   -> atr:ae op
                   -> a:s
                   -> btr:ae op
                   -> b:s
                   -> Tot (b1:bool {(b1 = true) <==> 
                              (sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\ 
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. (memq e a /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. (memq e b /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                              (forall e. mem_id e (diff_s (tolist a) (tolist l)) ==> not (mem_id e (diff_s (tolist b) (tolist l))))/\
                              (forall e. mem_id e (diff_s (tolist b) (tolist l)) ==> not (mem_id e (diff_s (tolist a) (tolist l)))))})

#set-options "--z3rlimit 10000"
let pre_cond_merge ltr l atr a btr b = 
  pre_cond_merge_1 ltr l atr a btr b &&
  pre_cond_merge_3 ltr l atr a btr b &&
  sim ltr l && sim (union ltr atr) a && sim (union ltr btr) b &&
  forallb (fun (e:(nat * nat)) -> not (mem_id (get_id e) (diff_s (tolist b) (tolist l)))) (diff_s (tolist a) (tolist l)) &&
  forallb (fun (e:(nat * nat)) -> not (mem_id (get_id e) (diff_s (tolist a) (tolist l)))) (diff_s (tolist b) (tolist l))

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\ 
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. (memq e a /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. (memq e b /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                              (forall e. mem_id e (diff_s (tolist a) (tolist l)) ==> not (mem_id e (diff_s (tolist b) (tolist l))))/\
                              (forall e. mem_id e (diff_s (tolist b) (tolist l)) ==> not (mem_id e (diff_s (tolist a) (tolist l))))))
                   (ensures (fun res -> res = merge_s l a b))

#set-options "--initial_fuel 5 --ifuel 5 --initial_ifuel 5 --fuel 5 --z3rlimit 100"

let merge ltr l atr a btr b =
  merge_s l a b

val pre_cond_op : s1:s -> op1:(nat * op) -> Tot bool
let pre_cond_op s1 op = (not (mem_id (get_id op) s1.front)) && (not (mem_id (get_id op) s1.back)) && (if is_dequeue op then (return op) = peek s1 else true)

val merge0 : ltr:ae op
           -> l:s
           -> atr:ae op
           -> a:s
           -> btr:ae op
           -> b:s
           -> Lemma (requires (sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\ 
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. (memq e a /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. (memq e b /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                          (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                              (forall e. mem_id e (diff_s (tolist a) (tolist l)) ==> not (mem_id e (diff_s (tolist b) (tolist l))))/\
                              (forall e. mem_id e (diff_s (tolist b) (tolist l)) ==> not (mem_id e (diff_s (tolist a) (tolist l))))))

                   (ensures ((forall e e1. ((memq e l /\ memq e1 l /\ fst e <> fst e1 /\ order e e1 (tolist l) /\ memq e (merge ltr l atr a btr b) /\
                                             memq e1 (merge ltr l atr a btr b)) \/
                                          (memq e a /\ memq e1 a /\ fst e <> fst e1 /\ order e e1 (tolist a) /\ memq e (merge ltr l atr a btr b) /\
                                            memq e1 (merge ltr l atr a btr b)) \/
                                          (memq e b /\ memq e1 b /\ fst e <> fst e1 /\ order e e1 (tolist b) /\ memq e (merge ltr l atr a btr b) /\
                                            memq e1 (merge ltr l atr a btr b)) \/
                                          (memq e l /\ mem e1 (diff_s (tolist a) (tolist l)) /\ fst e <> fst e1 /\ memq e (merge ltr l atr a btr b) /\
                                            memq e1 (merge ltr l atr a btr b)) \/
                                          (memq e l /\ mem e1 (diff_s (tolist b) (tolist l)) /\ fst e <> fst e1 /\ memq e (merge ltr l atr a btr b) /\
                                            memq e1 (merge ltr l atr a btr b)) \/
                                          (((mem e (diff_s (tolist a) (tolist l)) /\ mem e1 (diff_s (tolist b) (tolist l))) \/
                                            (mem e (diff_s (tolist b) (tolist l)) /\ mem e1 (diff_s (tolist a) (tolist l)))) /\ (fst e < fst e1))) <==>
                                          (memq e (merge ltr l atr a btr b) /\ memq e1 (merge ltr l atr a btr b) /\ fst e <> fst e1 /\
                                            order e e1 (tolist (merge ltr l atr a btr b)))))) [SMTPat (merge ltr l atr a btr b)]

let merge0 ltr l atr a btr b =
  let res = merge_s l a b in
  assert(forall e e1. ((memq e l /\ memq e1 l /\ fst e <> fst e1 /\ order e e1 (tolist l) /\ memq e res /\ memq e1 res) \/
                        (memq e a /\ memq e1 a /\ fst e <> fst e1 /\ order e e1 (tolist a) /\ memq e res /\ memq e1 res) \/
                        (memq e b /\ memq e1 b /\ fst e <> fst e1 /\ order e e1 (tolist b) /\ memq e res /\ memq e1 res) \/
                        (memq e l /\ mem e1 (diff_s (tolist a) (tolist l)) /\ fst e <> fst e1 /\ memq e res /\ memq e1 res) \/
                        (memq e l /\ mem e1 (diff_s (tolist b) (tolist l)) /\ fst e <> fst e1 /\ memq e res /\ memq e1 res) \/
                        (((mem e (diff_s (tolist a) (tolist l)) /\ mem e1 (diff_s (tolist b) (tolist l))) \/
                          (mem e1 (diff_s (tolist a) (tolist l)) /\ mem e (diff_s (tolist b) (tolist l)))) /\ (fst e < fst e1))) ==>
                            (memq e res /\ memq e1 res /\ fst e <> fst e1 /\ order e e1 (tolist res)));
  assert(forall e e1. ((memq e res /\ memq e1 res /\ fst e <> fst e1 /\ order e e1 (tolist res)) ==>
                        (memq e l /\ memq e1 l /\ fst e <> fst e1 /\ order e e1 (tolist l) /\ memq e res /\ memq e1 res) \/
                        (memq e a /\ memq e1 a /\ fst e <> fst e1 /\ order e e1 (tolist a) /\ memq e res /\ memq e1 res) \/
                        (memq e b /\ memq e1 b /\ fst e <> fst e1 /\ order e e1 (tolist b) /\ memq e res /\ memq e1 res) \/
                        (memq e l /\ mem e1 (diff_s (tolist a) (tolist l)) /\ fst e <> fst e1 /\ memq e res /\ memq e1 res) \/
                        (memq e l /\ mem e1 (diff_s (tolist b) (tolist l)) /\ fst e <> fst e1 /\ memq e res /\ memq e1 res) \/
                        (((mem e (diff_s (tolist a) (tolist l)) /\ mem e1 (diff_s (tolist b) (tolist l))) \/
                        (mem e1 (diff_s (tolist a) (tolist l)) /\ mem e (diff_s (tolist b) (tolist l)))) /\ (fst e < fst e1))))

val absmerge01 : ltr:ae op
               -> atr:ae op
               -> btr:ae op
               -> Lemma
                 (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                         (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                         (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)))
                 (ensures (forall x. (mem x (filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l)) ==>
                 mem x (absmerge ltr atr btr).l /\ ~(exists d. mem d (absmerge ltr atr btr).l /\
                                 is_dequeue d /\ mem d (absmerge ltr atr btr).l /\ get_id x <> get_id d /\ matched x d (absmerge ltr atr btr))))

#push-options "--initial_fuel 10 --ifuel 10 --initial_ifuel 10 --fuel 10 --z3rlimit 100000"

let absmerge01 ltr atr btr =
  let enq_list = filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l in
  let enq_list1 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  let enq_list2 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (ltr).l (fun d -> is_dequeue d && mem d (ltr).l && mem x (ltr).l &&
                                                                  get_id x <> get_id d && matched x d (ltr)))
                                               && not (exists_mem (atr).l (fun d -> is_dequeue d && mem d (atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (btr).l (fun d -> is_dequeue d && mem d (btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  assert(forall e. mem e enq_list1 <==> mem e enq_list2);
  assert(forall e. mem e enq_list2 ==> mem e enq_list)

#pop-options

type prop_merge_requires (ltr:ae op) (l:s) (atr:ae op) (a:s) (btr:ae op) (b:s)
                         = (sorted (tolist l) /\ sorted (tolist a) /\ sorted (tolist b) /\ 
                              (forall e. mem e ltr.l ==> ~(mem_id (get_id e) atr.l)) /\
                              (forall e. mem e ltr.l ==> ~(mem_id (get_id e) btr.l)) /\
                              (forall e. mem e atr.l ==> ~(mem_id (get_id e) btr.l)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist a) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. mem e (tolist l) /\ mem e1 (tolist b) /\ not (mem e1 (tolist l)) ==> (fst e) < (fst e1)) /\
                              (forall e e1. (memq e a /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                              (forall e e1. (memq e b /\ memq e1 l /\ (fst e = fst e1)) ==> (snd e = snd e1)) /\
                            (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist a) /\ mem e1 (tolist a) /\ order e e1 (tolist l) ==> order e e1 (tolist a)) /\
                            (forall e e1. mem e (tolist l) /\ mem e1 (tolist l) /\ mem e (tolist b) /\ mem e1 (tolist b) /\ order e e1 (tolist l) ==> order e e1 (tolist b)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                              (forall e. mem_id e (diff_s (tolist a) (tolist l)) ==> ~(mem_id e (diff_s (tolist b) (tolist l))))/\
                              (forall e. mem_id e (diff_s (tolist b) (tolist l)) ==> ~(mem_id e (diff_s (tolist a) (tolist l)))))

val prop_merge04  : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (forall e. mem e (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                     mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)
                                     /\ mem e ltr.l ==>
                                       ((mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l)))))

#set-options "--z3rlimit 10000"
let prop_merge04  ltr l atr a btr b =
  absmerge01 ltr atr btr;
  let enq_list = filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l in
  let enq_list1 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  assert(forall x. mem x enq_list /\ mem x ltr.l ==> (mem x ltr.l
                                               && not (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l &&
                                                                  get_id x <> get_id d && matched x d ltr))
                                               && not (exists_mem atr.l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem btr.l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))));
  ()

val prop_merge03  : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (forall e. ((mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l))) ==>
                                (mem e (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                     mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)
                                     /\ mem e ltr.l)))

let prop_merge03  ltr l atr a btr b =
  absmerge01 ltr atr btr;
  let enq_list = filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l in
  let enq_list1 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  assert(forall e. mem e enq_list1 ==> mem e enq_list /\ mem e ltr.l);
  ()

val prop_merge02  : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (forall e. (mem e (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                     mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)
                                     /\ mem e ltr.l) <==>
                                       ((mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l)))))

let prop_merge02  ltr l atr a btr b =
  absmerge01 ltr atr btr; prop_merge03 ltr l atr a btr b; prop_merge04 ltr l atr a btr b;
  let enq_list = filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l in
  let enq_list1 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  assert(forall e. mem e enq_list1 ==> mem e enq_list /\ mem e ltr.l);
  assert(forall x. mem x enq_list /\ mem x ltr.l ==> (mem x ltr.l
                                               && not (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l &&
                                                                  get_id x <> get_id d && matched x d ltr))
                                               && not (exists_mem atr.l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem btr.l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))));
  ()

#set-options "--initial_fuel 5 --ifuel 5 --initial_ifuel 5 --fuel 5 --z3rlimit 10000"

val prop_merge05 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (forall e. mem e (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                     mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) ==>
                                       ((mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                                   (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l)) \/

                                        (mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                                   (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l)) \/

                                        (mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l)))))
                       [SMTPat (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b))]

let prop_merge05 ltr l atr a btr b =
  absmerge01 ltr atr btr; prop_merge03 ltr l atr a btr b; prop_merge04 ltr l atr a btr b; prop_merge02 ltr l atr a btr b;
  let enq_list = filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l in
  let enq_list1 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                                   (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in
  let enq_list2 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                                   (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in
  let enq_list3 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  assert(forall x. mem x enq_list  ==> ((mem x enq_list1) \/ (mem x enq_list2) \/ (mem x ltr.l))); ()

val prop_merge06 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (forall e. ((mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                                   (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l)) \/

                                        (mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                                   (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l)) \/

                                        (mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l))) ==>

                                (mem e (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                     mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l))))
                       [SMTPat (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b))]

let prop_merge06 ltr l atr a btr b =
  prop_merge02 ltr l atr a btr b;
  let enq_list = filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l in
  let enq_list1 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                                   (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in
  let enq_list2 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                                   (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in
  let enq_list3 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  assert(forall e. ((mem e enq_list1) \/ (mem e enq_list2) \/ (mem e enq_list3)) ==> mem e enq_list); ()

val prop_merge01 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (forall e. mem e (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                     mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) <==>
                                       ((mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                                   (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l)) \/

                                        (mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                                   (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l)) \/

                                        (mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l)))))
                       [SMTPat (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b))]

let prop_merge01 ltr l atr a btr b =
  prop_merge02 ltr l atr a btr b; prop_merge05 ltr l atr a btr b; prop_merge06 ltr l atr a btr b;
  let enq_list = filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                   (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l in
  let enq_list1 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                                   (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in
  let enq_list2 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                                   (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in
  let enq_list3 = filter_op (fun x -> is_enqueue x && mem x ltr.l
                                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr atr)))
                                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                                                  get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in
  assert(forall e. ((mem e enq_list1) \/ (mem e enq_list2) \/ (mem e enq_list3)) ==> mem e enq_list);
  assert(forall x. mem x enq_list  ==> ((mem x enq_list1) \/ (mem x enq_list2) \/ (mem x enq_list3))); ()

val prop_merge001 : ltr:ae op
                  -> l:s
                  -> atr:ae op
                  -> a:s
                  -> btr:ae op
                  -> b:s
                  -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                          (ensures (forall_mem (tolist (merge ltr l atr a btr b)) (fun e -> mem (fst e, Enqueue (snd e))
                                            (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                              (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                              mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr))))
                                              (absmerge ltr atr btr).l))))

#reset-options

#set-options "--query_stats --initial_fuel 7 --ifuel 7 --initial_ifuel 7 --fuel 7 --z3rlimit 10000"

val prop_merge0011 : ltr:ae op
                  -> l:s
                  -> atr:ae op
                  -> a:s
                  -> btr:ae op
                  -> b:s
                  -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                          (ensures (forall e. (memq e a /\ memq e b /\ memq e l) ==>
                                                mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                             mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)))

#set-options "--z3rlimit 1000"
let prop_merge0011 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e. ((memq e a /\ memq e b /\ memq e l)) ==>
                     mem (fst e, Enqueue (snd e)) enq_list);

  ()

val prop_merge0012 : ltr:ae op
                  -> l:s
                  -> atr:ae op
                  -> a:s
                  -> btr:ae op
                  -> b:s
                  -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                          (ensures (forall e. (mem e (diff_s (tolist a) (tolist l))) ==>
                                                mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                             mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)))

#set-options "--z3rlimit 1000"
let prop_merge0012 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e. ((mem e (diff_s (tolist a) (tolist l)))) ==>
                     mem (fst e, Enqueue (snd e)) enq_list);
  ()

val prop_merge0013 : ltr:ae op
                  -> l:s
                  -> atr:ae op
                  -> a:s
                  -> btr:ae op
                  -> b:s
                  -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                          (ensures (forall e. (mem e (diff_s (tolist b) (tolist l))) ==>
                                                mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                             mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)))

#set-options "--z3rlimit 1000"
let prop_merge0013 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e. ((mem e (diff_s (tolist b) (tolist l)))) ==>
                     mem (fst e, Enqueue (snd e)) enq_list);
  ()

#set-options "--z3rlimit 1000"
let prop_merge001 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge0011 ltr l atr a btr b; prop_merge0012 ltr l atr a btr b; prop_merge0013 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e. ((memq e a /\ memq e b /\ memq e l) \/ (mem e (diff_s (tolist a) (tolist l))) \/ (mem e (diff_s (tolist b) (tolist l)))) ==>
                     mem (fst e, Enqueue (snd e)) enq_list);
  assert(forall e. ((memq e a /\ memq e b /\ memq e l) \/ (mem e (diff_s (tolist a) (tolist l))) \/ (mem e (diff_s (tolist b) (tolist l)))) <==>
                     memq e s0);
  assert(forall e. memq e s0 ==> mem (fst e, Enqueue (snd e)) enq_list);
  assert(forall_mem (tolist s0) (fun e -> mem (fst e, Enqueue (snd e)) enq_list));
  ()

#set-options "--z3rlimit 1000"
val prop_merge002 : ltr:ae op
                  -> l:s
                  -> atr:ae op
                  -> a:s
                  -> btr:ae op
                  -> b:s
                  -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                          (ensures (forall_mem (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l &&
                                                not (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                                mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr))))
                                                (absmerge ltr atr btr).l) (fun x -> mem x (absmerge ltr atr btr).l && is_enqueue x &&
                                                  mem ((get_id x), (get_ele x)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 1000"
let prop_merge002 ltr l atr a btr b = 
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e. (mem e enq_list6) \/ (mem e enq_list4) \/ (mem e enq_list5) ==> mem e enq_list); 
  prop_merge01 ltr l atr a btr b; prop_merge02 ltr l atr a btr b; prop_merge03 ltr l atr a btr b; 
  prop_merge04 ltr l atr a btr b; prop_merge05 ltr l atr a btr b; prop_merge06 ltr l atr a btr b;
  prop_merge001  ltr l atr a btr b; prop_merge0012 ltr l atr a btr b;
  prop_merge0013 ltr l atr a btr b; prop_merge0011 ltr l atr a btr b;
  assert(forall e. (mem e enq_list6) \/ (mem e enq_list4) \/ (mem e enq_list5) ==> memq (get_id e, get_ele e) s0);
  assert(forall e. mem e enq_list ==> ((mem e enq_list4) \/ (mem e enq_list5) \/ (mem e enq_list6))); 
  assert((forall e. mem e enq_list ==> ((mem e enq_list4) \/ (mem e enq_list5) \/ (mem e enq_list6))) /\
           (forall e. ((mem e enq_list4) \/ (mem e enq_list5) \/ (mem e enq_list6)) ==> memq (get_id e, get_ele e) s0) ==>
             (forall e. mem e enq_list ==> memq (get_id e, get_ele e) s0)); 
  assert(forall e. mem e enq_list ==> memq (get_id e, get_ele e) s0); 
  ()

val prop_merge00 : tr:ae op
                 -> s0:s
                  -> Lemma (requires true)
                          (ensures (forall (enq_list:list (nat * op)). ((forall_mem (filter_op (fun x -> is_enqueue x && mem x tr.l && 
                 not (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l &&
                 mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l) (fun x -> mem x tr.l && is_enqueue x &&
                 mem ((get_id x), (get_ele x)) (tolist s0))) /\ (enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && (forall_mem (filter_op (fun d -> is_dequeue d && mem d tr.l && get_id d <> get_id x) tr.l) (fun d -> get_id x <> get_id d && not (matched x d tr)))) tr.l)) ==> (forall_mem enq_list (fun x -> mem x tr.l && is_enqueue x && mem ((get_id x), (get_ele x)) (tolist s0)))))

#set-options "--z3rlimit 1000"
let prop_merge00 tr s0 = ()

val prop_merge0 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 1000"
let prop_merge0 ltr l atr a btr b = 
 let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  assert (forall e. mem e tr.l <==> mem e (absmerge ltr atr btr).l); 
  assert (forall e e1. mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1 <==> mem e (absmerge ltr atr btr).l /\ mem e1 (absmerge ltr atr btr).l /\ get_id e <> get_id e1 /\ (absmerge ltr atr btr).vis e e1); 
  let (enq_list:list (nat * op)) = filter_op (fun x -> is_enqueue x && mem x tr.l &&
                             (forall_mem (filter_op (fun d -> is_dequeue d && mem d tr.l && get_id d <> get_id x) tr.l) (fun d -> get_id x <> get_id d && not (matched x d tr)))) tr.l in
  prop_merge001 ltr l atr a btr b;
  assert (forall_mem (tolist (merge ltr l atr a btr b)) (fun x -> mem ((fst x), Enqueue (snd x)) enq_list)); 

  prop_merge002 ltr l atr a btr b;
 
  assert (forall_mem (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l &&
                                                    not (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                                    mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr))))
                                                    (absmerge ltr atr btr).l) (fun x -> mem x (absmerge ltr atr btr).l && is_enqueue x &&
                                                    mem ((get_id x), (get_ele x)) (tolist (merge ltr l atr a btr b)))); 
   prop_merge00 (absmerge ltr atr btr) (merge ltr l atr a btr b); 
 assert (forall_mem (filter_op (fun x -> is_enqueue x && mem x tr.l && 
     not (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l &&
     mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l) (fun x -> mem x tr.l && is_enqueue x &&
     mem ((get_id x), (get_ele x)) (tolist (merge ltr l atr a btr b)))); 
 assert (((forall_mem (filter_op (fun x -> is_enqueue x && mem x tr.l && 
    not (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l &&
    mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l) (fun x -> mem x tr.l && is_enqueue x &&
    mem ((get_id x), (get_ele x)) (tolist (merge ltr l atr a btr b)))) /\ (enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && (forall_mem (filter_op (fun d -> is_dequeue d && mem d tr.l && get_id d <> get_id x) tr.l) (fun d -> get_id x <> get_id d && not (matched x d tr)))) tr.l)) ==> (forall_mem enq_list (fun x -> mem x tr.l && is_enqueue x && mem ((get_id x), (get_ele x)) (tolist (merge ltr l atr a btr b))))); 

  assert (forall_mem enq_list (fun x -> mem x (absmerge ltr atr btr).l && is_enqueue x && mem ((get_id x), (get_ele x)) (tolist (merge ltr l atr a btr b)))); 
  assert (((forall_mem (tolist (merge ltr l atr a btr b)) (fun x -> mem ((fst x), Enqueue (snd x)) enq_list)) /\
                      (forall_mem enq_list (fun x -> mem x (absmerge ltr atr btr).l && is_enqueue x && mem ((get_id x), (get_ele x)) (tolist (merge ltr l atr a btr b))))) ==>  ((forall e. memq e (merge ltr l atr a btr b) <==> (mem (fst e, Enqueue (snd e)) (absmerge ltr atr btr).l /\ (forall d. mem d (absmerge ltr atr btr).l /\ fst e <> get_id d /\ is_dequeue d ==> (not (matched (fst e, Enqueue (snd e)) d (absmerge ltr atr btr)))))))); 
  assert (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b));
   ()

#pop-options

val prop_merge11 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. (memq e a /\ memq e1 a /\ not(memq e l) /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge11 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. memq e a /\ memq e1 a /\ not(memq e l) /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       ((atr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not (atr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                atr.vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()

val prop_merge12 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. (memq e b /\ memq e1 b /\ not(memq e l) /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge12 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. memq e b /\ memq e1 b /\ not(memq e l) /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       ((btr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not (btr.vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                btr.vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()


val prop_merge13 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. (memq e a /\ memq e1 b /\ not(memq e l) /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge13 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. not (memq e l) /\ memq e a /\ not (memq e1 l) /\ memq e1 b /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not ((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()

val prop_merge14 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. (memq e b /\ memq e1 a /\ not(memq e l) /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge14 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. not (memq e l) /\ memq e b /\ not (memq e1 l) /\ memq e1 a /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not ((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()

val prop_merge15 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. ((memq e l /\ memq e a /\ memq e b) /\ memq e1 a /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge15 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. (memq e l /\ memq e a /\ memq e b) /\ memq e1 a /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not ((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()

val prop_merge16 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. ((memq e l /\ memq e a /\ memq e b) /\ memq e1 b /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge16 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. (memq e l /\ memq e a /\ memq e b) /\ memq e1 b /\ not(memq e1 l) /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not ((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()

val prop_merge17 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. ((memq e1 l /\ memq e1 a /\ memq e1 b) /\ memq e a /\ not(memq e l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge17 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. (memq e1 l /\ memq e1 a /\ memq e1 b) /\ memq e a /\ not(memq e l) /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not ((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()

val prop_merge18 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. ((memq e1 l /\ memq e1 a /\ memq e1 b) /\ memq e b /\ not(memq e l) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge18 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. (memq e1 l /\ memq e1 a /\ memq e1 b) /\ memq e b /\ not(memq e l) /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not ((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()


val prop_merge19 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))

                       (ensures (forall e e1. ((memq e1 l /\ memq e1 a /\ memq e1 b) /\ (memq e l /\ memq e a /\ memq e b) /\ order e e1 (tolist (merge ltr l atr a btr b))) ==>
                                   (mem (fst e, Enqueue (snd e)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\

                                   mem (fst e1, Enqueue (snd e1)) (filter_op (fun x -> is_enqueue x && mem x (absmerge ltr atr btr).l && not
                                     (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l &&
                                       mem x (absmerge ltr atr btr).l && get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l) /\
                                         fst e <> fst e1 /\

                                        (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) \/
                                                 (~((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) \/
                                                 (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) /\
                                                 (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))
    ))
    )))

let prop_merge19 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  assert(forall e e1. (memq e1 l /\ memq e1 a /\ memq e1 b) /\ (memq e l /\ memq e a /\ memq e b) /\ order e e1 (tolist (merge ltr l atr a btr b)) ==>
                    (mem (fst e, Enqueue (snd e)) (enq_list) && mem (fst e1, Enqueue (snd e1)) (enq_list) && fst e <> fst e1 &&
                       (((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1))) ||
                         (not ((absmerge ltr atr btr).vis (fst e, Enqueue (snd e)) (fst e1, Enqueue (snd e1)) ||
                                (absmerge ltr atr btr).vis (fst e1, Enqueue (snd e1)) (fst e, Enqueue (snd e))) &&
                   (get_id (fst e, Enqueue (snd e)) < get_id (fst e1, Enqueue (snd e1)))))
  ));
  ()


val prop_merge1 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (sim1 (absmerge ltr atr btr) (merge ltr l atr a btr b)))

let prop_merge1 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  prop_merge11 ltr l atr a btr b; prop_merge12 ltr l atr a btr b; prop_merge13 ltr l atr a btr b; prop_merge14 ltr l atr a btr b;
  prop_merge15 ltr l atr a btr b; prop_merge16 ltr l atr a btr b; prop_merge17 ltr l atr a btr b; prop_merge18 ltr l atr a btr b;
  prop_merge19 ltr l atr a btr b;
  ()


val prop_merge21 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 1000"
let prop_merge21 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  assert(forall e e1. mem e (enq_list4) /\ mem e1 (enq_list4) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && (tr.vis e e1)) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()


val prop_merge22 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 1000"
let prop_merge22 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  assert(forall e e1. mem e (enq_list5) /\ mem e1 (enq_list5) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((tr.vis e e1))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge23 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b))
                                      )))

#set-options "--z3rlimit 1000"
let prop_merge23 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  assert(forall e e1. mem e (enq_list5) /\ mem e1 (enq_list5) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)
                                      ));

  ()
  
val prop_merge24 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b))
                                      )))

#set-options "--z3rlimit 1000"
let prop_merge24 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  assert(forall e e1. mem e (enq_list4) /\ mem e1 (enq_list4) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)
                                      ));

  ()

val prop_merge25 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge25 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  assert(forall e e1. mem e (enq_list5) /\ mem e1 (enq_list4) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && (tr.vis e e1)) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge26 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge26 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  assert(forall e e1. mem e (enq_list4) /\ mem e1 (enq_list5) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((tr.vis e e1))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge27 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge27 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  assert(forall e e1. mem e (enq_list4) /\ mem e1 (enq_list5) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()
  

val prop_merge28 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge28 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  assert(forall e e1. mem e (enq_list5) /\ mem e1 (enq_list4) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge29 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge29 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list6) /\ mem e1 (enq_list4) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && (tr.vis e e1)) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge210 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge210 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list6) /\ mem e1 (enq_list5) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((tr.vis e e1))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge211 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge211 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list5) /\ mem e1 (enq_list6) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge212 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge212 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list4) /\ mem e1 (enq_list6) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()


val prop_merge213 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge213 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list5) /\ mem e1 (enq_list6) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && (tr.vis e e1)) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge214 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge214 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list4) /\ mem e1 (enq_list6) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((tr.vis e e1))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge215 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge215 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list5 = filter_op (fun x -> is_enqueue x && mem x btr.l && not
                             (exists_mem btr.l (fun d -> is_dequeue d && mem d btr.l && mem x btr.l && get_id x <> get_id d && matched x d btr))) btr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list6) /\ mem e1 (enq_list5) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()


val prop_merge216 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge216 ltr l atr a btr b =
  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list4 = filter_op (fun x -> is_enqueue x && mem x atr.l && not
                             (exists_mem atr.l (fun d -> is_dequeue d && mem d atr.l && mem x atr.l && get_id x <> get_id d && matched x d atr))) atr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list6) /\ mem e1 (enq_list4) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge218 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((not ((absmerge ltr atr btr).vis e e1 ||
                               (absmerge ltr atr btr).vis e1 e) && (get_id e < get_id e1)))) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge218 ltr l atr a btr b =
  absmerge01 ltr atr btr; prop_merge02 ltr l atr a btr b;  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b;
  prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list6) /\ mem e1 (enq_list6) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((not (tr.vis e e1 || tr.vis e1 e) && (get_id e < get_id e1)))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()


val prop_merge217 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b) /\
                              (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))
                       (ensures (forall e e1. mem e (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               mem e1 (filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l) /\
                               get_id e <> get_id e1 /\ mem e1
                             (filter_op (fun e1 -> get_id e <> get_id e1 && ((absmerge ltr atr btr).vis e e1)) (filter_op (fun x ->
                               is_enqueue x && mem x (absmerge ltr atr btr).l && not
                             (exists_mem (absmerge ltr atr btr).l (fun d -> is_dequeue d && mem d (absmerge ltr atr btr).l && mem x (absmerge ltr atr btr).l &&
                               get_id x <> get_id d && matched x d (absmerge ltr atr btr)))) (absmerge ltr atr btr).l)) ==>
                          (memq ((get_id e), (get_ele e)) (merge ltr l atr a btr b) /\ memq ((get_id e1), (get_ele e1)) (merge ltr l atr a btr b) /\
                                get_id e <> get_id e1 /\ order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist (merge ltr l atr a btr b)))))

#set-options "--z3rlimit 10000"
let prop_merge217 ltr l atr a btr b =
  absmerge01 ltr atr btr; prop_merge02 ltr l atr a btr b;  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b; prop_merge002 ltr l atr a btr b;
  prop_merge0 ltr l atr a btr b;
  let tr = absmerge ltr atr btr in
  let s0 = merge ltr l atr a btr b in
  let enq_list = filter_op (fun x -> is_enqueue x && mem x tr.l && not
                             (exists_mem tr.l (fun d -> is_dequeue d && mem d tr.l && mem x tr.l && get_id x <> get_id d && matched x d tr))) tr.l in

  let enq_list6 = filter_op (fun x -> is_enqueue x && mem x ltr.l && not
                             (exists_mem ltr.l (fun d -> is_dequeue d && mem d ltr.l && mem x ltr.l && get_id x <> get_id d && matched x d ltr))
                               && not (exists_mem (union ltr atr).l (fun d -> is_dequeue d && mem d (union ltr atr).l && mem x (union ltr atr).l &&
                                         get_id x <> get_id d && matched x d (union ltr atr)))
                               && not (exists_mem (union ltr btr).l (fun d -> is_dequeue d && mem d (union ltr btr).l && mem x (union ltr btr).l &&
                                         get_id x <> get_id d && matched x d (union ltr btr)))) ltr.l in

  assert(forall e e1. mem e (enq_list6) /\ mem e1 (enq_list6) /\ get_id e <> get_id e1 /\ mem e1
           (filter_op (fun e1 -> get_id e <> get_id e1 && ((tr.vis e e1))) (enq_list)) ==>
                          (memq ((get_id e), (get_ele e)) s0 /\ memq ((get_id e1), (get_ele e1)) s0 /\ get_id e <> get_id e1 /\
                                      order ((get_id e), (get_ele e)) ((get_id e1), (get_ele e1)) (tolist s0)));

  ()

val prop_merge2 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (sim2 (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000"
let prop_merge2 ltr l atr a btr b =
  absmerge01 ltr atr btr; prop_merge02 ltr l atr a btr b;  prop_merge01 ltr l atr a btr b; prop_merge001 ltr l atr a btr b;
  prop_merge002 ltr l atr a btr b; prop_merge0 ltr l atr a btr b; prop_merge21 ltr l atr a btr b; prop_merge22 ltr l atr a btr b;
  prop_merge23 ltr l atr a btr b; prop_merge24 ltr l atr a btr b; prop_merge25 ltr l atr a btr b; prop_merge26 ltr l atr a btr b;
  prop_merge27 ltr l atr a btr b; prop_merge28 ltr l atr a btr b; prop_merge29 ltr l atr a btr b; prop_merge210 ltr l atr a btr b;
  prop_merge211 ltr l atr a btr b; prop_merge212 ltr l atr a btr b; prop_merge213 ltr l atr a btr b; prop_merge214 ltr l atr a btr b;
  prop_merge215 ltr l atr a btr b; prop_merge216 ltr l atr a btr b; prop_merge217 ltr l atr a btr b; prop_merge218 ltr l atr a btr b;
  ()

val prop_merge : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 100"
let prop_merge ltr l atr a btr b =
  prop_merge0 ltr l atr a btr b;
  prop_merge1 ltr l atr a btr b;
  prop_merge2 ltr l atr a btr b


val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a) /\ (sim tr b))
                        (ensures (forall e. memq e a <==> memq e b) /\
                                 (forall e e1. memq e a /\ memq e1 a /\ fst e <> fst e1 /\ order e e1 (tolist a) <==>
                                          memq e b /\ memq e1 b /\ fst e <> fst e1 /\ order e e1 (tolist b)))

#set-options "--z3rlimit 100"
let convergence tr a b = ()

val prop_oper0: tr:ae op
                -> st:s
                -> op:(nat * op)
                -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\ 
                                  (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                        (ensures (is_empty st ==> (sim (append tr op) (get_st (app_op st op)))))

let prop_oper0 tr st op = ()

val prop_oper1: tr:ae op
                  -> st:s
                  -> op:(nat * op)
                  -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\ 
                                    (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                          (ensures (not (is_empty st) /\ is_enqueue op ==> (sim0 (append tr op) (get_st (app_op st op)))))
#set-options "--z3rlimit  1000"
let prop_oper1 tr st op =  ()

val prop_oper3: tr:ae op
                -> st:s
                -> op:(nat * op)
                -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                  (is_dequeue op ==> return op = peek st) /\ 
                                  (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                        (ensures (not (is_empty st) /\ is_dequeue op ==> (sim0 (append tr op) (get_st (app_op st op)))))
#set-options "--z3rlimit  1000"
let prop_oper3 tr st op = ()

val prop_oper2: tr:ae op
                -> st:s
                -> op:(nat * op)
                -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\ 
                                  (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                        (ensures ((is_enqueue op) /\ not (is_empty st) ==> (sim1 (append tr op) (get_st (app_op st op)))))
#set-options "--z3rlimit  1000"
let prop_oper2 tr st op = ()

val prop_oper5: tr:ae op
                  -> st:s
                  -> op:(nat * op)
                  -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\ 
                                    (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                          (ensures (not (is_empty st) /\ is_enqueue op ==> (sim2 (append tr op) (get_st (app_op st op)))))
#set-options "--z3rlimit  1000"
let prop_oper5 tr st op = ()

val prop_oper4: tr:ae op
                -> st:s
                -> op:(nat * op)
                -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                  (is_dequeue op ==> return op = peek st) /\ 
                                  (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                        (ensures (not (is_empty st) /\ is_dequeue op ==> (sim1 (append tr op) (get_st (app_op st op)))))
#set-options "--z3rlimit  1000"
let prop_oper4 tr st op = ()

val prop_oper6: tr:ae op
                -> st:s
                -> op:(nat * op)
                -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                  (is_dequeue op ==> return op = peek st) /\ 
                                  (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                        (ensures (not (is_empty st) /\ is_dequeue op ==> (sim2 (append tr op) (get_st (app_op st op)))))
#set-options "--z3rlimit  1000"
let prop_oper6 tr st op = ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                get_id op > 0 /\ pre_cond_op st op /\ 
                                (forall e. mem e tr.l ==> get_id e < get_id op))
                         (ensures (sim (append tr op) (get_st (app_op st op))))
let prop_oper tr st op =
  prop_oper0 tr st op;
  prop_oper1 tr st op;
  prop_oper2 tr st op;
  prop_oper3 tr st op;
  prop_oper4 tr st op;
  prop_oper5 tr st op;
  prop_oper6 tr st op;
  ()

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures ((Rd? (get_op op)) ==> (forall e. memq e (extract (get_rval (app_op st op))) <==> memq e (extract (spec op tr))) /\
                               (forall e e1. memq e (extract (get_rval (app_op st op))) /\ memq e1 (extract (get_rval (app_op st op))) /\ fst e <> fst e1 /\ order e e1 (tolist (extract (get_rval (app_op st op)))) <==>
                                        memq e (extract (spec op tr)) /\ memq e1 (extract (spec op tr)) /\ fst e <> fst e1 /\ order e e1 (tolist (extract (spec op tr))))) /\ 
                               ((Enqueue? (get_op op) \/ Dequeue? (get_op op)) ==> (get_rval (app_op st op) = (spec op tr))))
let prop_spec tr st op = ()

(*)instance _ : mrdt s op = {
  Library_old.init = init;
  Library_old.sim = sim;
  Library_old.pre_cond_op = pre_cond_op;
  Library_old.app_op = app_op;
  Library_old.prop_oper = prop_oper;
  Library_old.pre_cond_merge1 = pre_cond_merge1;
  Library_old.pre_cond_merge = pre_cond_merge;
  Library_old.merge1 = merge_s;
  Library_old.merge = merge;
  Library_old.prop_merge = prop_merge;
  Library_old.convergence = convergence
}*)


