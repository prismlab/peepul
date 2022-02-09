module Nn_ctr

open FStar.List.Tot

type s = x:(Icounter1.s * Icounter1.s){fst x >= snd x}

type op =
  | Inc
  | Dec : (option nat) -> op

type o = (nat * op)

let get_id (id,_) = id
let get_op (_,op) = op

val incr: s1:s -> Tot (s0:s{s0 = (fst s1 + 1, snd s1)})
let incr s = (fst s + 1, snd s)

val decr: s1:s -> Tot (s0:(option nat * s){((fst s1 - snd s1 = 0) ==> (snd s0) = s1 /\ None? (fst s0)) /\
                                              ((fst s1 - snd s1 > 0) ==> (snd s0) = (fst s1, snd s1 + 1) /\ Some? (fst s0))})
let decr s = if (fst s > snd s) then (Some (fst s - snd s), (fst s, snd s + 1)) else (None, s)

val return : d:o{Dec? (snd d)} -> Tot (v:option nat{d = (get_id d, (Dec v))})
let return (_, Dec x) = x

val unopt : #t:eqtype -> x:option t{Some? x} -> Tot (y:t{x = Some y})
let unopt (Some x) = x

val app_op: s1:s -> op:o -> Tot (s0:s{(Inc? (snd op) ==> s0 = (fst s1 + 1, snd s1)) /\
                                     (Dec? (snd op) ==> (((fst s1 - snd s1 = 0) ==> s0 = s1) /\
                                                       ((fst s1 - snd s1 > 0) ==> s0 = (fst s1, snd s1 + 1))))
                                   })
let app_op st op = match op with
  | _, Inc -> incr st
  | _, Dec x -> snd (decr st)

val member : id:nat
           -> l:list o
           -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member n l =
  match l with
  | [] -> false
  | (id, _)::xs -> (n = id) || member n xs

val unique : l:list o
           -> Tot bool
let rec unique l =
  match l with
  | [] -> true
  | (id, _)::xs -> not (member id xs) && unique xs

noeq type ae =
     |A : vis:(o -> o -> Tot bool) -> l:list o {unique l} -> ae

assume val axiom_ae : l:ae
                   -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\
                           get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*) /\
                           (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                           (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*) ))
                           [SMTPat (unique l.l)]

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

val filter_op : f:(o -> bool)
           -> l:list o{unique l}
           -> Tot (l1:list o {(forall e. mem e l1 <==> (mem e l /\ f e)) /\ unique l1 /\ (forall e1 e2. mem e1 l /\ mem e2 l /\ f e1 /\ f e2 /\ ord e1 e2 l ==> ord e1 e2 l1)})
let rec filter_op f l =
  match l with
  | [] -> []
  | hd::tl -> if f hd then hd::(filter_op f tl) else filter_op f tl

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

val ctr : s0:s -> Tot (z:int{z = fst s0 - snd s0})
let ctr s = fst s - snd s

val matched : i:o -> d:o -> tr:ae
            -> Pure bool (requires (get_id i <> get_id d))
                        (ensures (fun b -> (Inc? (get_op i) /\ Dec? (get_op d) /\ mem i tr.l /\ mem d tr.l /\ (return d) = Some (get_id i) /\ (tr.vis i d)) <==>
                          (b = true)))
let matched i d tr = (Inc? (snd i) && Dec? (snd d)) && (mem i tr.l && mem d tr.l) && (return d) = Some (get_id i) && (tr.vis i d)

#set-options "--initial_fuel 7 --ifuel 7 --initial_ifuel 7 --fuel 7 --z3rlimit 10000"

val isum : l:(list o){forall i. mem i l ==> Inc? (snd i)}
        -> Tot nat (decreases %[l])
let rec isum l =
  match l with
  | [] -> 0
  | (_, Inc)::xs -> 1 + isum xs

val dsum : l:(list o){forall i. mem i l ==> Dec? (snd i)}
        -> Tot nat (decreases %[l])
let rec dsum l =
  match l with
  | [] -> 0
  | (_, Dec _)::xs -> 1 + dsum xs

val sim0 : tr:ae
         -> s0:s
         -> Tot (b:bool{b = true <==> (fst s0 = isum (filter_op (fun x -> Inc? (snd x)) tr.l))})

let sim0 tr s0 = (fst s0 = isum (filter_op (fun x -> Inc? (snd x)) tr.l))

val sim1 : tr:ae
         -> s0:s
         -> Tot (b:bool{b = true <==> (fst s0 - snd s0 = isum (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l))})

let sim1 tr s0 = (fst s0 - snd s0 = isum (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l))

val sim : tr:ae
        -> s0:s
        -> Tot (b:bool{b = true <==> (fst s0 = isum (filter_op (fun x -> Inc? (snd x)) tr.l)) /\
                                (fst s0 - snd s0 = isum (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l))})

let sim tr s0 = sim0 tr s0 && sim1 tr s0

val convergence : tr:ae
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (a = b))
let convergence tr a b = ()

val append : tr:ae
             -> op:o
             -> Pure ae
               (requires (not (member (get_id op) tr.l))  /\ (forall e. mem e tr.l ==> get_id e < get_id op))
               (ensures (fun res -> (forall e. mem e res.l <==> (mem e tr.l \/ e = op)) /\
                        (forall e1 e2. mem e1 tr.l /\ mem e2 tr.l /\ get_id e1 <> get_id e2 /\ tr.vis e1 e2 ==> res.vis e1 e2) /\
                        (forall e. mem e tr.l ==> res.vis e op)))
let append tr op =
    match tr with
    |(A _ ops) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                              (mem o tr.l && o1 = op && get_id o <> get_id op)) (op::ops))

val sorted: (o -> o -> Tot bool) -> list o -> Tot bool
let rec sorted f = function
  | x::y::xs -> f x y && sorted f (y::xs)
  | _ -> true

type total_order (a:eqtype) =
  f:(a -> a -> Tot bool) { (forall a1 a2. f a1 a2 \/ f a2 a1) // total
  }

val count: o -> list o -> Tot nat
let rec count x = function
  | hd::tl -> (if hd = x then 1 else 0) + count x tl
  | [] -> 0


val mem_count: x:o -> l:list o ->
  Lemma (requires True)
	(ensures (mem x l = (count x l > 0)))
	(decreases l)
  [SMTPat (mem x l)]
let rec mem_count x = function
  | [] -> ()
  | _::tl -> mem_count x tl

val partition: (o -> Tot bool) -> list o -> Tot (list o * list o)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
    let l1, l2 = partition f tl in
    if f hd then (hd::l1, l2) else (l1, hd::l2)


val partition_lemma: f:(o -> Tot bool) -> l:list o ->
  Lemma (requires True)
        (ensures (let (hi, lo) = partition f l in
                  length l = length hi + length lo
                  /\ (forall x.{:pattern f x} (mem x hi ==>   f x)
                                      /\ (mem x lo ==> ~(f x)))
                  /\ (forall x.{:pattern (count x hi) \/ (count x lo)}
                                   (count x l = count x hi + count x lo))))
  [SMTPat (partition f l)]
let rec partition_lemma f l = match l with
  | [] -> ()
  | hd::tl ->  partition_lemma f tl

val sorted_app_lemma: f:total_order o
  -> l1:list o{sorted f l1} -> l2:list o{sorted f l2} -> pivot:o
  -> Lemma (requires (forall y. (mem y l1 ==> ~(f pivot y))
		        /\ (mem y l2 ==>   f pivot y)))
          (ensures (sorted f (l1 @ pivot :: l2)))
  [SMTPat (sorted f (l1 @ pivot::l2))]
let rec sorted_app_lemma f l1 l2 pivot =
  match l1 with
  | hd::tl -> sorted_app_lemma f tl l2 pivot
  | _ -> ()

type is_permutation (l:list o) (m:list o) =
  forall x. count x l = count x m

val append_count: l:list o -> m:list o -> x:o ->
  Lemma (requires True)
        (ensures (count x (l @ m) = (count x l + count x m)))
  [SMTPat (count x (l @ m))]
let rec append_count l m x =
  match l with
  | [] -> ()
  | hd::tl -> append_count tl m x

let permutation_app_lemma (hd:o) (tl:list o)
                          (l1:list o) (l2:list o)
   : Lemma (requires (is_permutation tl (l1 @ l2)))
           (ensures (is_permutation (hd::tl) (l1 @ (hd::l2))))
   = //NS: 05/15/2017
     //This proof required an interesting change following issue #1028
     //From append_count, we can automatically prove what the assert below says
     //However, what we get from append_count is
     //    count' ZFuel x (l1 @ (hd :: l2)) = count' ZFuel x l1 + count' ZFuel x (hd :: l2))
     //where count' is the fuel-instrumented variant of count
     //But, this variant prevents further progress, since we can't unfold the last term in the sum
     //By assertion the equality, we explicitly introduce `count x (hd::l2)`
     //which can then be unfolded as needed.
     //This is rather counterintuitive.
    assert (forall x. count x (l1 @ (hd :: l2)) = count x l1 + count x (hd :: l2))


val quicksort: f:total_order o -> l:list o ->
  Tot (m:list o{sorted f m /\ is_permutation l m})
  (decreases (length l))
let rec quicksort f l =
  match l with
  | [] -> []
  | pivot::tl ->
    let hi, lo = partition (f pivot) tl in
    let m = quicksort f lo @ pivot :: quicksort f hi in
    permutation_app_lemma pivot tl (quicksort f lo) (quicksort f hi);
    m


// val sorted: list o -> Tot bool
// let rec sorted l = match l with
//     | [] | [_] -> true
//     | x::y::xs -> (fst x <= fst y) && (sorted (y::xs))

// val test_sorted: x:o -> l:list o ->
//       Lemma ((sorted (x::l) /\ Cons? l) ==> fst x <= fst (Cons?.hd l))
// let test_sorted x l = ()

// val test_sorted2: unit -> Tot (m:list o{sorted m})
// let test_sorted2 () = Nil

// (* Fact about sorted *)
// val sorted_smaller: x:o
//                 ->  y:o
//                 ->  l:list o
//                 ->  Lemma (requires (sorted (x::l) /\ mem y l))
//                           (ensures (fst x <= fst y))
//                           [SMTPat (sorted (x::l)); SMTPat (mem y l)]
// let rec sorted_smaller x y l = match l with
//     | [] -> ()
//     | z::zs -> if z=y then () else sorted_smaller x y zs


// type permutation (l1:list o) (l2:list o) =
//     length l1 = length l2 /\ (forall n. mem n l1 = mem n l2)

// type permutation_2 (l:list o) (l1:list o) (l2:list o) =
//     (forall n. mem n l = (mem n l1 || mem n l2)) /\
//     length l = length l1 + length l2

// val insert : i:o -> l:list o{sorted l} ->
//       Tot (m:list o{sorted m /\ permutation (i::l) m})
// let rec insert i l = match l with
//   | [] -> [i]
//   | hd::tl ->
//      if fst i <= fst hd then i::l
//      else let i_tl = insert i tl in
//           let (z::_) = i_tl in
//           if mem z tl then sorted_smaller hd z tl;
//           hd::i_tl

// (* Insertion sort *)
// val sort : l:list o -> Tot (m:list o{sorted m /\ permutation l m})
// let rec sort l = match l with
//     | [] -> []
//     | x::xs -> insert x (sort xs)

val oldest_incr : tr:ae
                -> Tot (op:option o{(Some? op ==> (forall e. Inc? (snd e) /\ mem e tr.l /\
                                 (forall d. get_id e <> get_id d /\ Dec? (snd d) /\ mem d tr.l ==> not(matched e d tr)) /\ (fst (unopt op) <> fst e) ==>
                                       tr.vis (unopt op) e \/ (fst (unopt op) < fst e)) /\ mem (unopt op) tr.l /\ Inc? (snd (unopt op))) /\
                        (None? op ==> (forall i. Inc? (snd i) /\ mem i tr.l ==> (exists d. Dec? (snd d) /\ mem d tr.l /\ get_id d <> get_id i /\ matched i d tr)))})

#set-options "--query_stats --initial_fuel 10 --ifuel 10 --initial_ifuel 10 --fuel 10 --z3rlimit 10000000000"


let oldest_incr tr =
  let unmatched_incr = filter_op (fun i -> Inc? (snd i) && not (exists_mem tr.l
                                        (fun d -> get_id i <> get_id d && Dec? (snd d) && matched i d tr))) tr.l in
  let old_incr = filter_op (fun i -> Inc? (snd i) && not (exists_mem unmatched_incr (fun i1 -> Inc? (snd i1) && get_id i <> get_id i1 && mem i1 unmatched_incr &&
                 (tr.vis i1 i)))) unmatched_incr in
  match old_incr with
  | [] -> assert(forall i i1. mem i unmatched_incr /\ mem i1 unmatched_incr ==> tr.vis i i1 \/ tr.vis i1 i \/ (not (tr.vis i i1) && not (tr.vis i1 i)));
         assert(forall i. mem i unmatched_incr /\ not (mem i old_incr) ==> (exists i1. mem i1 unmatched_incr /\ fst i <> fst i1 ==> tr.vis i1 i));
         // assert(old_incr = []);
         // assert(forall i. mem i unmatched_incr ==> (exists_mem unmatched_incr (fun i1 -> Inc? (snd i1) && get_id i <> get_id i1 && mem i1 unmatched_incr &&
         //         (tr.vis i1 i))));
         // assert(unmatched_incr = []);
         admit(); None
  | x::xs -> // assert(exists i. Inc? (snd i) /\ mem i tr.l /\ (forall d. Dec? (snd d) /\ mem d tr.l /\ get_id i <> get_id d ==> not(matched i d tr)));
         // assert(exists i. Inc? (snd i) /\ mem i tr.l /\ forall_mem unmatched_incr (fun i1 -> Inc? (snd i1) && (tr.vis i i1 ||
         //                       (not (tr.vis i i1) && not (tr.vis i1 i)))));
         // let op_l = (quicksort (fun x y -> fst x <= fst y) old_incr) in
         // let op = (hd op_l) in
         // assert(length xs >= 1);
         // assert(unique (quicksort (fun x y -> fst x <= fst y) old_incr));
         // assert(unique old_incr);
         // assert(unique op_l);
         // assert(forall f x. unique x ==> unique (quicksort f x));
         // assert(forall e. Inc? (snd e) /\ mem e tr.l /\
         //                         (forall d. get_id e <> get_id d /\ Dec? (snd d) /\ mem d tr.l ==> not(matched e d tr)) ==>
         //                               mem e unmatched_incr);
         // assert(forall e. mem e old_incr ==> (not (tr.vis (unopt op) e) /\ not (tr.vis e (unopt op))));
         // assert(forall e. mem e old_incr /\ fst op <> fst e ==> fst op < fst e);
         admit(); Some (hd (quicksort (fun x y -> fst x < fst y) old_incr))


val prop_oper0 : tr:ae
               -> st:s
               -> op:o
               -> Lemma (requires (sim tr st) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                (not (member (get_id op) tr.l)))
                      (ensures ((Inc? (snd op)) ==> sim0 (append tr op) (app_op st op)))

let prop_oper0 tr st op = ()

val prop_oper1 : tr:ae
              -> st:s
              -> op:o
              -> Lemma (requires (sim tr st) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                (not (member (get_id op) tr.l)))
                      (ensures ((Dec? (snd op)) ==> sim0 (append tr op) (app_op st op)))

let prop_oper1 tr st op = ()

val prop_oper3 : tr:ae
               -> st:s
               -> op:o
               -> Lemma (requires (sim tr st) /\ (Dec? (snd op)) /\ (fst st - snd st <= 0) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 (return op = None) /\
                                 (not (member (get_id op) tr.l)))
                       (ensures (sim1 (append tr op) (app_op st op)))

#set-options "--initial_fuel 5 --ifuel 5 --initial_ifuel 5 --fuel 5 --z3rlimit 10000000"

let prop_oper3 tr st op = admit(); ()

val filter_op0 : f:(o -> bool)
           -> l:list o{unique l}
           -> Lemma (requires (forall x. mem x l ==> ~(f x))) (ensures (filter_op f l = [])) [SMTPat (filter_op f l)]

let rec filter_op0 f l =
  match l with
  | [] -> ()
  | hd::tl -> filter_op0 f tl

// Try: Rewrite everything "sort" related without the specialized compare function. Just use fun x y -> fst x <= fst y
val prop_oper02 : l:list o{(forall i. mem i l ==> Inc? (snd i)) /\ (unique l)} -> l1:list o{(forall i. mem i l1 ==> Inc? (snd i)) /\ (forall i. mem i l1 ==> mem i l) /\ (unique l1)}
                ->  op:o{Inc? (snd op) /\ mem op l /\ (forall e. mem e l1 ==> get_id e < get_id op)}
                -> Lemma (requires (forall i. mem i l <==> mem i l1 \/ i = op))
                        (ensures (isum l = isum l1 + 1))

let prop_oper02 l l1 op =
  let f = (fun (x:o) (y:o) -> fst x <= fst y) in
  let l = quicksort f l in
  let l1 = quicksort f l1 in
  let is = isum l in
  let is1 = isum l1 in
  assert(mem op l);
  assert(forall x. mem x l1 ==> mem x l);
  // assert(forall x y. mem x l1 /\ mem y l1 /\ fst x <> fst y /\ ord x y l1 ==> fst x < fst y);
  // assert(forall x y. mem x l /\ mem y l /\ fst x <> fst y /\ ord x y l ==> fst x < fst y);
  // assert(l = l1 @ [op]);
  // assert(length l = length l1 + 1);
  // assert(is = is1 + 1);
  admit(); ()

val prop_oper2 : tr:ae
               -> st:s
               -> op:o
               -> Lemma (requires (sim tr st) /\ (Inc? (snd op)) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 (not (member (get_id op) tr.l)))
                       (ensures (sim1 (append tr op) (app_op st op)))

#set-options "--query_stats --initial_fuel 10 --ifuel 10 --initial_ifuel 10 --fuel 10 --z3rlimit 10000000000"

let prop_oper2 tr st op = assert(fst st + 1 = fst (app_op st op));
                          assert(snd st = snd (app_op st op));

                          assert(isum (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l) = (fst st - snd st));

                          assert(forall i. mem i (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l) \/ i = op ==>
                                mem i (filter_op (fun x -> Inc? (snd x) &&
                                not (exists_mem (append tr op).l (fun y -> get_id x <> get_id y && Dec?
                                                (snd y) && matched x y (append tr op)))) (append tr op).l));

                          assert(forall i. mem i (filter_op (fun x -> Inc? (snd x) &&
                                not (exists_mem (append tr op).l (fun y -> get_id x <> get_id y && Dec? (snd y) &&
                                  matched x y (append tr op)))) (append tr op).l)
                                ==> mem i (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l) \/ i = op);

                          assert(forall i. (mem i (filter_op (fun x -> Inc? (snd x) &&
                                not (exists_mem (append tr op).l (fun y -> get_id x <> get_id y && Dec? (snd y) &&
                                    matched x y (append tr op)))) (append tr op).l))
                                <==> (mem i (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l) \/ i = op));

                          assert((append tr op).l = op::(tr.l));

                          prop_oper02 (filter_op (fun x -> Inc? (snd x) &&
                                not (exists_mem (append tr op).l (fun y -> get_id x <> get_id y && Dec? (snd y) &&
                                    matched x y (append tr op)))) (append tr op).l)
                                    (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l)  op;

                          assert(isum (filter_op (fun x -> Inc? (snd x) &&
                                not (exists_mem (append tr op).l (fun y -> get_id x <> get_id y && Dec? (snd y) &&
                                    matched x y (append tr op)))) (append tr op).l) = isum (filter_op (fun x -> Inc? (snd x) &&
                                       not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l) + 1);

                          assert(sim1 (append tr op) (app_op st op));  ()

val prop_oper4 : tr:ae
               -> st:s
               -> op:o
               -> Lemma (requires (sim tr st) /\ (Dec? (snd op)) /\ (fst st - snd st > 0) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 (return op = Some (get_id (unopt (oldest_incr tr)))) /\ (not (member (get_id op) tr.l)))
                       (ensures (sim1 (append tr op) (app_op st op)))


let prop_oper4 tr st op = assert(fst st = fst (app_op st op));
                          assert(snd st + 1 = snd (app_op st op));
                          assert(exists i. Inc? (snd i) /\ mem i tr.l /\ i = (unopt (oldest_incr tr)));
                          assert(exists i. mem i (append tr op).l /\ mem op (append tr op).l /\ Inc? (snd i) /\ Dec? (snd op) /\ get_id op <> get_id i /\
                                      matched i op (append tr op));
                          // assert(isum (filter_op (fun x -> Inc? (snd x) &&
                          //              not (exists_mem (append tr op).l (fun y -> get_id x <> get_id y && Dec? (snd y) &&
                          //              matched x y (append tr op)))) (append tr op).l) =
                          //         isum (filter_op (fun x -> Inc? (snd x) &&
                          //              not (exists_mem tr.l (fun y -> get_id x <> get_id y && Dec? (snd y) && matched x y tr))) tr.l) - 1);
                          admit(); ()


val prop_oper : tr:ae
               -> st:s
               -> op:o
               -> Lemma (requires (sim tr st) /\ (not (member (get_id op) tr.l)) /\ (forall e. mem e tr.l ==> get_id e < get_id op) /\
                                 ((Dec? (snd op)) /\ (fst st - snd st > 0) ==> (return op = Some (get_id (unopt (oldest_incr tr))))) /\
                                 (((Dec? (snd op)) /\ fst st - snd st <= 0) ==> (return op = None)))
                       (ensures (sim (append tr op) (app_op st op)))

let prop_oper tr st op =
  match op with
  | (_, Inc) -> prop_oper0 tr st op; prop_oper2 tr st op
  | (_, Dec _) -> match (fst st - snd st > 0) with
                 | true -> prop_oper1 tr st op; prop_oper4 tr st op
                 | false -> prop_oper1 tr st op; prop_oper3 tr st op

val num_decr: l:s -> a:s{fst a >= fst l /\ snd a >= snd l} -> Tot (n:nat{((fst l - snd l) < (snd a - snd l) ==> n = (fst l - snd l)) /\
                                                                        ((fst l - snd l) >= (snd a - snd l) ==> n = (snd a - snd l))})
let num_decr l a = match (fst l - snd l) < (snd a - snd l) with
| false -> (snd a - snd l)
| true -> (fst l - snd l)

val common_decr: l:s -> a:s{fst a >= fst l /\ snd a >= snd l} -> b:s{fst b >= fst l /\ snd b >= snd l}
                 -> Tot (n:nat{n = min (num_decr l a) (num_decr l b)})
let common_decr l a b = min (num_decr l a) (num_decr l b)

val merge_s: l:s -> a:s{fst a >= fst l /\ snd a >= snd l} -> b:s{fst b >= fst l /\ snd b >= snd l} ->
             Tot (res:s{res = (fst a + fst b - fst l, snd a + snd b - snd l - common_decr l a b)})

let merge_s l a b =
  let cd = common_decr l a b in
  let fst_r = fst a + fst b - fst l in
  let snd_r = snd a + snd b - snd l in
  (fst_r, snd_r - cd)

val union_list_ae : l:ae
                  -> a:ae
                  -> Pure (list o)
                         (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))) /\ (forall e e1. mem e l.l /\ mem e1 a.l ==> get_id e < get_id e1))
                         (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique u))) (decreases %[l.l;a.l])
let rec union_list_ae l a =
  match l,a with
  |(A _ []), (A _ []) -> []
  |(A _ (x::xs)), _ -> x::(union_list_ae (A l.vis xs) a)
  |(A _ []), (A _ (x::xs)) -> x::(union_list_ae l (A a.vis xs))

val union : l:ae
          -> a:ae
          -> Pure ae
            (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))) /\ (forall e e1. (mem e l.l /\ mem e1 a.l ==> get_id e < get_id e1)))
            (ensures (fun u -> (forall e e1. (mem e u.l /\ mem e1 u.l /\ get_id e <> get_id e1 /\ u.vis e e1) <==>
                                     ((mem e l.l /\ mem e1 l.l /\ get_id e <> get_id e1 /\ l.vis e e1) \/
                                     (mem e a.l /\ mem e1 a.l /\ get_id e <> get_id e1 /\ a.vis e e1) \/
                                     (mem e l.l /\ mem e1 a.l /\ get_id e <> get_id e1))) /\
                             (forall e e1. (mem e u.l /\ mem e1 u.l /\ get_id e <> get_id e1 /\ ~(u.vis e e1 \/ u.vis e1 e)) <==>
                                     ((mem e l.l /\ mem e1 l.l /\ get_id e <> get_id e1 /\ ~(l.vis e e1 \/ l.vis e1 e)) \/
                                     (mem e a.l /\ mem e1 a.l /\ get_id e <> get_id e1 /\ ~(a.vis e e1 \/ a.vis e1 e)))) /\
                             (forall e d. (mem e u.l /\ mem d u.l /\ get_id e <> get_id d /\ matched e d u) <==>
                                        ((mem e l.l /\ mem d l.l /\ get_id e <> get_id d /\ matched e d l) \/
                                         (mem e a.l /\ mem d a.l /\ get_id e <> get_id d /\ matched e d a) \/
                                         (Inc? (snd e) /\ Dec? (snd d) /\ mem e l.l /\ mem d a.l /\ (Some? (return d)) /\
                                               (return d = Some (fst e)) /\ (u.vis e d)))
    )))

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
                                      (forall e. mem e l.l ==> not (member (get_id e) b.l)) /\
                                      (forall e e1. (mem e l.l /\ mem e1 a.l ==> get_id e < get_id e1)) /\
                                      (forall e e1. (mem e l.l /\ mem e1 b.l ==> get_id e < get_id e1)))
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
                         (forall e. mem e l.l ==> not (member (get_id e) b.l)) /\
                         (forall e e1. (mem e l.l /\ mem e1 a.l ==> get_id e < get_id e1)) /\
                         (forall e e1. (mem e l.l /\ mem e1 b.l ==> get_id e < get_id e1)))
               (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                               (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2) <==>
                                         ((mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/
                                         (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ (union l a).vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ (union l b).vis e1 e2))) /\
                                (forall e e1. (mem e u.l /\ mem e1 u.l /\ get_id e <> get_id e1 /\ ~(u.vis e e1 \/ u.vis e1 e)) <==>
                                         ((((mem e a.l /\ mem e1 b.l) \/ (mem e1 a.l /\ mem e b.l)) /\ (get_id e <> get_id e1)) \/
                                         (mem e a.l /\ mem e1 a.l /\ get_id e <> get_id e1 /\ ~(a.vis e e1 \/ a.vis e1 e)) \/
                                         (mem e b.l /\ mem e1 b.l /\ get_id e <> get_id e1 /\ ~(b.vis e e1 \/ b.vis e1 e)) \/
                                         (mem e l.l /\ mem e1 l.l /\ get_id e <> get_id e1 /\ ~(l.vis e e1 \/ l.vis e1 e)))) /\
                                (forall e d. (mem e u.l /\ mem d u.l /\ get_id e <> get_id d /\ matched e d u) <==>
                                        ((mem e l.l /\ mem d l.l /\ get_id e <> get_id d /\ matched e d l) \/
                                         (mem e a.l /\ mem d a.l /\ get_id e <> get_id d /\ matched e d a) \/
                                         (mem e b.l /\ mem d b.l /\ get_id e <> get_id d /\ matched e d b) \/
                                         (mem e l.l /\ mem d a.l /\ get_id e <> get_id d /\ matched e d (union l a)) \/
                                         (mem e l.l /\ mem d b.l /\ get_id e <> get_id d /\ matched e d (union l b))))
                                         ))

let absmerge l a b =
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) ||
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1 && (union l a).vis o o1) ||
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1 && (union l b).vis o o1)) (absmerge_list_ae l a b))

val merge: ltr:ae
           -> l:s
           -> atr:ae
           -> a:s
           -> btr:ae
           -> b:s
           -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                              (forall e e1. (mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1)) /\
                              (forall e e1. (mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1)) /\
                             (fst a >= fst l /\ snd a >= snd l /\ fst b >= fst l /\ snd b >= snd l) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                    (ensures (fun res -> res = (fst a + fst b - fst l, snd a + snd b - snd l - common_decr l a b)))

let merge ltr l atr a btr b = merge_s l a b


type prop_merge_requires (ltr: ae) (l:s) (atr:ae) (a:s) (btr:ae) (b:s)
                         = ((forall e. mem e ltr.l ==> ~(member (get_id e) atr.l)) /\
                              (forall e. mem e ltr.l ==> ~(member (get_id e) btr.l)) /\
                              (forall e. mem e atr.l ==> ~(member (get_id e) btr.l)) /\
                              (fst a >= fst l /\ snd a >= snd l /\ fst b >= fst l /\ snd b >= snd l) /\
                              (forall e e1. (mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1)) /\
                              (forall e e1. (mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))

val incrsum : l:list o{unique l} -> Tot (res:nat{isum (filter_op (fun x -> Inc? (snd x)) l)  = res})
let incrsum l = isum (filter_op (fun x -> Inc? (snd x)) l)

val lemma0 : l:ae
           -> a:ae
           -> b:ae
           -> Lemma
             (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                       (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                       (forall e. mem e l.l ==> not (member (get_id e) b.l)) /\
                       (forall e e1. (mem e l.l /\ mem e1 a.l ==> get_id e < get_id e1)) /\
                       (forall e e1. (mem e l.l /\ mem e1 b.l ==> get_id e < get_id e1)))
             (ensures (forall e. mem e (absmerge_list_ae l a b) <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                      ((isum (filter_op (fun x -> Inc? (snd x)) (absmerge_list_ae l a b))) =
                             (isum (filter_op (fun x -> Inc? (snd x)) a.l)) +
                             (isum (filter_op (fun x -> Inc? (snd x)) b.l)) +
                             (isum (filter_op (fun x -> Inc? (snd x)) l.l))) /\
                        ((isum (filter_op (fun x -> Inc? (snd x)) (absmerge l a b).l)) =
                             (isum (filter_op (fun x -> Inc? (snd x)) a.l)) +
                             (isum (filter_op (fun x -> Inc? (snd x)) b.l)) +
                             (isum (filter_op (fun x -> Inc? (snd x)) l.l)))) (decreases %[l.l;a.l;b.l])

let rec lemma0 l a b =
    match l,a,b with
    |(A _ []), (A _ []), (A _ []) -> ()
    |(A _ (x::xs)), _, _ -> lemma0 (A l.vis xs) a b
    |(A _ []), (A _ (x::xs)), _ -> lemma0 l (A a.vis xs) b
    |(A _ []), (A _ []), (A _ (x::xs)) -> lemma0 l a (A b.vis xs)

val lemma1 : l:ae
           -> a:ae
           -> Lemma
             (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))) /\ (forall e e1. mem e l.l /\ mem e1 a.l ==> get_id e < get_id e1))
             (ensures (forall e. mem e (union_list_ae l a) <==> mem e l.l \/ mem e a.l) /\
                      ((isum (filter_op (fun x -> Inc? (snd x)) (union_list_ae l a))) =
                             (isum (filter_op (fun x -> Inc? (snd x)) l.l)) +
                             (isum (filter_op (fun x -> Inc? (snd x)) a.l))) /\
                       ((isum (filter_op (fun x -> Inc? (snd x)) (union l a).l)) =
                             (isum (filter_op (fun x -> Inc? (snd x)) l.l)) +
                             (isum (filter_op (fun x -> Inc? (snd x)) a.l))) /\
                      ((isum (filter_op (fun x -> Inc? (snd x)) a.l)) =
                             (isum (filter_op (fun x -> Inc? (snd x)) (union_list_ae l a))) -
                             (isum (filter_op (fun x -> Inc? (snd x)) l.l))) /\
                      ((isum (filter_op (fun x -> Inc? (snd x)) a.l)) =
                             (isum (filter_op (fun x -> Inc? (snd x)) (union l a).l)) -
                             (isum (filter_op (fun x -> Inc? (snd x)) l.l))) /\
                      ((isum (filter_op (fun x -> Inc? (snd x)) l.l)) =
                             (isum (filter_op (fun x -> Inc? (snd x)) (union_list_ae l a))) -
                             (isum (filter_op (fun x -> Inc? (snd x)) a.l))) /\
                       ((isum (filter_op (fun x -> Inc? (snd x)) l.l)) =
                              (isum (filter_op (fun x -> Inc? (snd x)) (union l a).l)) -
                              (isum (filter_op (fun x -> Inc? (snd x)) a.l)))) (decreases %[l.l;a.l])

let rec lemma1 l a =
  match l,a with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma1 (A l.vis xs) a
  |(A _ []), (A _ (x::xs)) -> lemma1 l (A a.vis xs)

val prop_merge0 : ltr: ae
                -> l:s
                -> atr:ae
                -> a:s
                -> btr:ae
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (sim0 (absmerge ltr atr btr) (merge ltr l atr a btr b)))

let prop_merge0 ltr l atr a btr b =
    lemma1 ltr atr;
    lemma1 ltr btr;
    lemma0 ltr atr btr; ()

val prop_merge1 : ltr: ae
                -> l:s
                -> atr:ae
                -> a:s
                -> btr:ae
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (sim1 (absmerge ltr atr btr) (merge ltr l atr a btr b)))

let prop_merge1 ltr l atr a btr b =
    let tr = (absmerge ltr atr btr) in
    let res = (merge ltr l atr a btr b) in
    assert(isum (filter_op (fun x -> Inc? (snd x)) (union ltr atr).l) = fst a);
    assert(isum (filter_op (fun x -> Inc? (snd x)) (union ltr btr).l) = fst b);
    assert(isum (filter_op (fun x -> Inc? (snd x)) ltr.l) = fst l);
    assert(forall i. Inc? (snd i) /\ mem i tr.l ==> mem i ltr.l \/ mem i (union ltr atr).l \/ mem i (union ltr btr).l);
    assert(forall i. Inc? (snd i) /\ mem i (union ltr atr).l ==> mem i ltr.l \/ mem i atr.l);
    // assert(isum (filter_op (fun x -> Inc? (snd x)) (union ltr atr).l) = isum (filter_op (fun x -> Inc? (snd x)) ltr.l) +
    //                                    isum (filter_op (fun x -> Inc? (snd x)) atr.l));
    admit(); ()

val prop_merge : ltr: ae
                -> l:s
                -> atr:ae
                -> a:s
                -> btr:ae
                -> b:s
                -> Lemma (requires (prop_merge_requires ltr l atr a btr b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

let prop_merge ltr l atr a btr b =
  prop_merge0 ltr l atr a btr b; prop_merge1 ltr l atr a btr b; ()


