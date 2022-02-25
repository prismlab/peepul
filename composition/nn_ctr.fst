module Nn_ctr
open FStar.List.Tot

open Library

val fst : nat * nat -> nat
let fst (p, n) = p
val snd : nat * nat -> nat
let snd (p, n) = n

type s = x:(nat * nat){fst x >= snd x}

type op =
  | Inc
  | Dec : (option nat) -> op

val opa : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id. op1 = (id,Inc))})
  let opa op1 =
    match op1 with
    |(id,Inc) -> true
    |_ -> false

val opr : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id id1. op1 = (id,Dec id1))})
  let opr op1 =
      match op1 with
      |(id,Dec _) -> true
      |_ -> false

val incr: s1:s -> Tot (s0:s{s0 = (fst s1 + 1, snd s1)})
let incr s = (fst s + 1, snd s)

val fst1 : option nat * s -> option nat
let fst1 (r, _) = r

val snd1 : option nat * s -> s
let snd1 (_, s) = s
  
val decr: s1:s -> Tot (s0:(option nat * s){((fst s1 - snd s1 = 0) ==> (snd1 s0) = s1 /\ None? (fst1 s0)) /\
                                              ((fst s1 - snd s1 > 0) ==> (snd1 s0) = (fst s1, snd s1 + 1) /\ Some? (fst1 s0))})
let decr s = if (fst s > snd s) then (Some (fst s - snd s), (fst s, snd s + 1)) else (None, s)

val return : d:(nat * op){Dec? (get_op d)} -> Tot (v:option nat{d = (get_id d, (Dec v))})
let return (_, Dec x) = x

val unopt : #t:eqtype -> x:option t{Some? x} -> Tot (y:t{x = Some y})
let unopt (Some x) = x

val app_op: s1:s -> op:(nat * op) -> Tot (s0:s{(Inc? (get_op op) ==> s0 = (fst s1 + 1, snd s1)) /\
                                     (Dec? (get_op op) ==> (((fst s1 - snd s1 = 0) ==> s0 = s1) /\
                                                       ((fst s1 - snd s1 > 0) ==> s0 = (fst s1, snd s1 + 1))))
                                   })
let app_op st op = match op with
  | _, Inc -> incr st
  | _, Dec x -> snd1 (decr st)

instance nnctr : datatype s op = {
  Library.app_op = app_op
}

val position_o : e:(nat * op)
             -> s1:(list (nat * op)) {mem e s1 /\ unique s1}
             -> Tot nat  (decreases (s1))
let rec position_o e s1 =
      match s1 with
      |x::xs -> if (e = x) then 0 else 1 + (position_o e xs)

val ord : e1:(nat * op)
          -> e2:(nat * op) {(get_id e1) <> (get_id e2)}
          -> s1:(list (nat * op)) {mem e1 s1 /\ mem e2 s1 /\ unique s1}
          -> Tot (r:bool {(position_o e1 s1 < position_o e2 s1) <==> r = true})
let ord e1 e2 s1 = (position_o e1 s1 < position_o e2 s1)

val ctr : s0:s -> Tot (z:nat {z = fst s0 - snd s0})
let ctr s = fst s - snd s

val matched : i:(nat * op) -> d:(nat * op) -> tr:ae op
            -> Pure bool (requires (get_id i <> get_id d))
                        (ensures (fun b -> (Inc? (get_op i) /\ Dec? (get_op d) /\ mem i tr.l /\ mem d tr.l /\ (return d) = Some (get_id i) /\ (tr.vis i d)) <==>
                          (b = true)))
let matched i d tr = (Inc? (get_op i) && Dec? (get_op d)) && (mem i tr.l && mem d tr.l) && (return d) = Some (get_id i) && (tr.vis i d)

#set-options "--initial_fuel 7 --ifuel 7 --initial_ifuel 7 --fuel 7 --z3rlimit 10000"

val filter_uni : f:((nat * op) -> bool)
                 -> l:list (nat * op) 
                 -> Lemma (requires (unique l))
                          (ensures (unique (filter f l)))
                          [SMTPat (filter f l)]
let rec filter_uni f l =
    match l with
    |[] -> ()
    |x::xs -> filter_uni f xs
    
val isum : l:(list (nat * op)){forall i. mem i l ==> Inc? (get_op i) /\ unique l}
        -> Tot nat (decreases %[l])
let rec isum l =
  match l with
  | [] -> 0
  | (_, Inc)::xs -> 1 + isum xs

val dsum : l:(list (nat * op)){forall i. mem i l ==> Dec? (get_op i) /\ unique l}
        -> Tot nat (decreases %[l])
let rec dsum l =
  match l with
  | [] -> 0
  | (_, Dec _)::xs -> 1 + dsum xs

val sim0 : tr:ae op
         -> s0:s
         -> Tot (b:bool{b = true <==> (fst s0 = isum (filter (fun x -> Inc? (get_op x)) tr.l))})
let sim0 tr s0 = (fst s0 = isum (filter (fun x -> Inc? (get_op x)) tr.l))

val sim1 : tr:ae op -> s0:s
           -> Tot (b:bool {b = true <==> (fst s0 - snd s0 = isum (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)))})
    let sim1 tr s0 = (fst s0 - snd s0 = isum (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)))


val sim : tr:ae op
         -> s0:s
           -> Tot (b:bool{b = true <==> sim0 tr s0 /\ sim1 tr s0})
let sim tr s0 = 
sim0 tr s0 && sim1 tr s0

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (fst a - snd a = fst b - snd b))
let convergence tr a b = ()

val prop_oper0 : tr:ae op
               -> st:s
                 -> op:(nat * op)
               -> Lemma (requires (sim tr st) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                (not (member (get_id op) tr.l)))
                      (ensures ((Inc? (get_op op)) ==> sim0 (append tr op) (app_op st op)))

let prop_oper0 tr st op = ()

val prop_oper1 : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                (not (member (get_id op) tr.l)))
                      (ensures ((Dec? (get_op op)) ==> sim0 (append tr op) (app_op st op)))

let prop_oper1 tr st op = ()

val help : tr:ae op -> s1:s
           -> Lemma (requires sim tr s1)
                   (ensures (fst s1 > snd s1 <==> (exists i. mem i tr.l /\ Inc? (get_op i) /\
                            (forall d. mem d tr.l /\ Dec? (get_op d) /\ get_id i <> get_id d ==> 
                                  not (matched i d tr)))))
                                  [SMTPat (sim tr s1)]
#set-options "--z3rlimit 10000000"
  let help tr s1 = ()

val help1 : tr:ae op -> s1:s
            -> Lemma (requires sim tr s1)
               (ensures (fst s1 <= snd s1 <==> (forall d. mem d tr.l ==> Dec? (get_op d)) \/ tr.l = [] \/
                             (forall i. mem i tr.l /\ Inc? (get_op i) ==>
              (exists d. mem d tr.l /\ Dec? (get_op d) /\ get_id i <> get_id d /\ matched i d tr))))
                    [SMTPat (sim tr s1)]
#set-options "--z3rlimit 10000000"
let help1 tr s1 = ()
  
val prop_oper3 : tr:ae op
               -> st:s
                 -> op:(nat * op)
               -> Lemma (requires (sim tr st) /\ (Dec? (get_op op)) /\ (fst st - snd st <= 0) /\ 
                                 (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 (return op = None) /\
                                 (not (member (get_id op) tr.l)))
                       (ensures (sim (append tr op) (app_op st op)))

#set-options "--initial_fuel 5 --ifuel 5 --initial_ifuel 5 --fuel 5 --z3rlimit 10000000"

let prop_oper3 tr st op = ()

val remove : a:list (nat * op){unique a}
             -> op1:(nat * op)
             -> Pure (list (nat * op))
                  (requires (mem op1 a))
         (ensures (fun l -> (forall e. mem e l <==> mem e a /\ e <> op1) /\ (unique l) /\ (length a = length l + 1)))

let rec remove a op = match a with
  | [] -> []
  | x::xs -> if x = op then xs else x::(remove xs op)

val filter_op0 : f:((nat * op) -> bool)
                         -> l:list (nat * op){unique l}
                   -> Lemma (requires (forall x. mem x l ==> ~(f x))) (ensures (filter f l = [])) [SMTPat (filter f l)]

let rec filter_op0 f l =
      match l with
      | [] -> ()
      | hd::tl -> filter_op0 f tl

val isum_len_lemma : l:list (nat * op){forall i. mem i l ==> Inc? (get_op i) /\ unique l} -> Lemma (ensures (length l = isum l)) [SMTPat (length l); SMTPat (isum l)]
  let rec isum_len_lemma l = match l with
    | [] -> ()
    | x::xs -> isum_len_lemma xs

val int_lemma : z:int -> Lemma (ensures (forall x y. x - (y + z) = x - y - z))
    let int_lemma z = ()

val sorted: list (nat * op) -> Tot bool
let rec sorted l = match l with
    | [] | [_] -> true
    | x::y::xs -> (get_id x <= get_id y) && (sorted (y::xs))

val test_sorted: x:(nat * op) -> l:list (nat * op) ->
      Lemma ((sorted (x::l) /\ Cons? l) ==> get_id x <= get_id (Cons?.hd l))
let test_sorted x l = ()

val test_sorted2: unit -> Tot (m:list (nat * op){sorted m})
let test_sorted2 () = Nil

val sorted_smaller: x:(nat * op)
                      ->  y:(nat * op)
                      ->  l:list (nat * op)
                ->  Lemma (requires (sorted (x::l) /\ mem y l))
                          (ensures (get_id x <= get_id y))
                          [SMTPat (sorted (x::l)); SMTPat (mem y l)]
let rec sorted_smaller x y l = match l with
    | [] -> ()
    | z::zs -> if z=y then () else sorted_smaller x y zs

type permutation (l1:list (nat * op)) (l2:list (nat * op)) =
    length l1 = length l2 /\ (forall n. mem n l1 = mem n l2)

type permutation_2 (l:list (nat * op)) (l1:list (nat * op)) (l2:list (nat * op)) =
    (forall n. mem n l = (mem n l1 || mem n l2)) /\
    length l = length l1 + length l2

val insert : i:(nat * op) -> l:list (nat * op){sorted l} ->
        Tot (m:list (nat * op){sorted m /\ permutation (i::l) m})
let rec insert i l = match l with
  | [] -> [i]
  | hd::tl ->
     if get_id i <= get_id hd then i::l
     else let i_tl = insert i tl in
          let (z::_) = i_tl in
          if mem z tl then sorted_smaller hd z tl;
          hd::i_tl

(* Insertion sort *)
val sort : l:list (nat * op) -> Tot (m:list (nat * op){sorted m /\ permutation l m})
let rec sort l = match l with
    | [] -> []
    | x::xs -> insert x (sort xs)

val uniq_len_lemma : l:list (nat * op) -> l1:list (nat * op)
         -> Lemma (requires (forall i. mem i l <==> mem i l1) /\ unique l /\ unique l1) 
                 (ensures (length l = length l1))
                     (decreases %[ l;  l1]) [SMTPat (unique l); SMTPat (unique l1)]

let rec uniq_len_lemma l l1 =
    match l, l1 with
    |[],[] -> ()
    |x::xs,_ -> uniq_len_lemma xs (remove l1 x)

val prop_oper002 : l:list (nat * op){(forall i. mem i l ==> Inc? (get_op i)) /\ (unique l)}
                 -> l1:list (nat * op){(forall i. mem i l1 ==> Inc? (get_op i)) /\ (forall i. mem i l1 ==> mem i l) /\ (unique l1)}
                 ->  op:(nat * op){Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op)}
                 -> Lemma (requires (forall i. mem i l <==> mem i l1 \/ i = op))
                        (ensures (length l = length l1 + 1)) (decreases %[l;l1])

let rec prop_oper002 l l1 op = match l with
  | [] -> ()
  | x::xs -> if mem x l1 then  prop_oper002 xs (remove l1 x) op
           else assert(x = op); ()

val prop_oper003 : l:list (nat * op){(forall i. mem i l ==> Inc? (get_op i)) /\ (unique l)}
                  -> l1:list (nat * op){(forall i. mem i l1 ==> Inc? (get_op i)) /\ (forall i. mem i l1 ==> mem i l) /\ (unique l1) /\
                                 (exists op. Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op))}
               (*)  ->  op:(nat * op){Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op)}*)
                        -> Lemma (requires (exists op. Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op) /\
                                          (forall i. mem i l <==> mem i l1 \/ i = op)))
                           (ensures (length l = length l1 + 1)) (decreases %[l;l1])

let rec prop_oper003 l l1 = match l with
    | [] -> ()
    | x::xs -> if mem x l1 then  prop_oper003 xs (remove l1 x) else ()

#push-options "--fuel 1"
val prop_oper02 : l:list (nat * op){(forall i. mem i l ==> Inc? (get_op i)) /\ (unique l)}
                  -> l1:list (nat * op){(forall i. mem i l1 ==> Inc? (get_op i)) /\ (forall i. mem i l1 ==> mem i l) /\ (unique l1)}
                  ->  op:(nat * op){Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op)}
                -> Lemma (requires (forall i. mem i l <==> mem i l1 \/ i = op))
                        (ensures (isum l = isum l1 + 1)) (decreases %[l;l1])
                       (*) [SMTPat (forall i. mem i l <==> mem i l1 \/ i = op)]*)
let prop_oper02 l l1 op = prop_oper002 l l1 op
#pop-options

val prop_oper03 : l:list (nat * op){(forall i. mem i l ==> Inc? (get_op i)) /\ (unique l)}
                 -> l1:list (nat * op){(forall i. mem i l1 ==> Inc? (get_op i)) /\ (forall i. mem i l1 ==> mem i l) /\ (unique l1) /\
                                   (exists op. Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op))}
                    (*)  ->  op:(nat * op){Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op)}*)
                         -> Lemma (requires (exists op. Inc? (get_op op) /\ (forall e. mem e l1 ==> get_id e <> get_id op) /\
                                           (forall i. mem i l <==> mem i l1 \/ i = op)))
                                 (ensures (isum l = isum l1 + 1))

let prop_oper03 l l1 = prop_oper003 l l1

val prop_oper2 : tr:ae op
               -> st:s
                 -> op:(nat * op)
             -> Lemma (requires (sim tr st) /\ (Inc? (get_op op)) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 (not (member (get_id op) tr.l)))
                       (ensures (sim1 (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper2 tr st op = assert(fst st + 1 = fst (app_op st op));
                          assert(snd st = snd (app_op st op)); 

                  assert(forall i. (mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) &&
    matched x y (append tr op)) (append tr op).l )) (filter (fun x -> Inc? (get_op x)) (append tr op).l)))
                                <==> (mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)) \/ i = op));

                          assert((append tr op).l = op::(tr.l));

    prop_oper02 (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) &&
            matched x y (append tr op)) (append tr op).l )) (filter (fun x -> Inc? (get_op x)) (append tr op).l))
                    (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)) op;

    assert (isum (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) &&
                         matched x y (append tr op)) (append tr op).l )) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) = isum (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)) + 1);

                          assert(sim1 (append tr op) (app_op st op));  ()

val prop_oper41 : tr:ae op
                   -> st:s
                   -> op:(nat * op)
                   -> Lemma (requires (sim tr st) /\ (Dec? (get_op op)) /\ (fst st - snd st > 0) /\ 
                                     (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                     (exists i. mem i tr.l /\ Inc? (get_op i) /\ (forall d. mem d tr.l /\ Dec? (get_op d) /\ 
                                     get_id i <> get_id d ==> not (matched i d tr)) /\
                           return op = Some (get_id i)) /\ (not (member (get_id op) tr.l)))
                          (ensures (forall i. mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) ==> mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l))))

#set-options "--z3rlimit 10000000"
let prop_oper41 tr st op = ()

val prop_oper42 : tr:ae op
                 -> st:s
                   -> op:(nat * op)
                 -> Lemma (requires (sim tr st) /\ (Dec? (get_op op)) /\ (fst st - snd st > 0) /\ 
                                   (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                   (exists i. mem i tr.l /\ Inc? (get_op i) /\ (forall d. mem d tr.l /\ Dec? (get_op d) /\ 
                                   get_id i <> get_id d ==> not (matched i d tr)) /\
                                   return op = Some (get_id i)) /\ (not (member (get_id op) tr.l)) /\
                 (forall i. mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) ==> mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l))) /\ (exists op1. Inc? (get_op op1) /\ (forall e. mem e (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) ==> get_id e <> get_id op1)))
                         (ensures (exists op1. Inc? (get_op op1) /\ (forall e. mem e (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) ==> get_id e <> get_id op1) /\ (forall i. mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)) <==> mem i (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) \/ i = op1)))

#set-options "--z3rlimit 10000000"
let prop_oper42 tr st op = ()

val prop_oper4 : tr:ae op
               -> st:s
                 -> op:(nat * op)
               -> Lemma (requires (sim tr st) /\ (Dec? (get_op op)) /\ (fst st - snd st > 0) /\ 
                                 (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 (exists i. mem i tr.l /\ Inc? (get_op i) /\ (forall d. mem d tr.l /\ Dec? (get_op d) /\ 
                                 get_id i <> get_id d ==> not (matched i d tr)) /\
                          return op = Some (get_id i)) /\ (not (member (get_id op) tr.l)))
                       (ensures (sim1 (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper4 tr st op =  
  assert(fst st = fst (app_op st op));
  assert(snd st + 1 = snd (app_op st op)); 
  assert (exists i. mem i tr.l /\ Inc? (get_op i) /\
            (forall d. mem d tr.l /\ Dec? (get_op d) /\ get_id i <> get_id d ==> not (matched i d tr)) /\
            matched i op (append tr op)); 
  assert ((forall e. mem e (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)) ==> Inc? (get_op e)) /\ 
      unique (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l))); 
      
  assert ((forall e. mem e (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) ==> Inc? (get_op e)) /\
        unique (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l))); 

  prop_oper41 tr st op;

   assert (exists op1. Inc? (get_op op1) /\ (forall e. mem e (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)) ==> get_id e <> get_id op1));

   prop_oper42 tr st op;

  prop_oper03 (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) (filter (fun x -> Inc? (get_op x)) tr.l)) (filter (fun x -> not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y (append tr op)) (append tr op).l)) (filter (fun x -> Inc? (get_op x)) (append tr op).l)); 

    assert (isum (filter (fun x -> Inc? (get_op x) &&
    not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) && matched x y tr) tr.l)) tr.l) = 
        isum (filter (fun x -> Inc? (get_op x) &&
                not (existsb (fun y -> get_id x <> get_id y && Dec? (get_op y) &&
              matched x y (append tr op)) (append tr op).l )) (append tr op).l) + 1);
 
  assert(sim1 (append tr op) (app_op st op)); ()

val prop_oper : tr:ae op
               -> st:s
                 -> op:(nat * op)
               -> Lemma (requires (sim tr st) /\ (not (member (get_id op) tr.l)) /\ 
                                 (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 ((Dec? (get_op op)) /\ (fst st - snd st > 0) ==> (exists i. mem i tr.l /\ Inc? (get_op i)
                                   /\ (forall d. mem d tr.l /\ Dec? (get_op d) /\
                                        get_id i <> get_id d ==> not(matched i d tr)) /\ return op = Some (get_id i))) /\
                                 (((Dec? (get_op op)) /\ fst st - snd st <= 0) ==> (return op = None)))
                       (ensures (sim (append tr op) (app_op st op)))

let prop_oper tr st op =
  match op with
  | (_, Inc) -> prop_oper0 tr st op; prop_oper2 tr st op
  | (_, Dec _) -> match (fst st - snd st > 0) with
                 | true -> prop_oper1 tr st op; prop_oper4 tr st op
                 | false -> prop_oper1 tr st op; prop_oper3 tr st op

