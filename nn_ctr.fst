module Nn_ctr
open FStar.List.Tot

#set-options "--query_stats"

open Library

type s = n:nat {n >= 0}

val init : s
let init = 0 

type rval = |Val : s -> rval
            |Bot

type op =
  |Inc                   //Increment 
  |Dec : option nat -> op //Decrement op contains the id of the increment op if it matched with it.
  |Rd                    //Read

let pre_cond_do s1 op = true

val do : s1:s
       -> op:(nat * op)
       -> Pure (s * rval)
         (requires pre_cond_do s1 op)
         (ensures (fun r -> (Inc? (get_op op) ==> r = (s1 + 1, Bot)) /\
                         (Dec? (get_op op) /\ s1 > 0 ==> r = (s1 - 1, Bot)) /\
                         (Dec? (get_op op) /\ s1 = 0 ==> r = (s1, Bot)) /\
                         (Rd? (get_op op) ==> r = (s1, Val s1))))
let do s1 op1 =
  match op1 with
  |(id, Inc) -> (s1 + 1, Bot)
  |(id, Dec x) -> ((if s1 > 0 then s1 - 1 else s1), Bot)
  |(id, Rd) -> (s1, Val s1)

val return : o:(nat * op){Dec? (get_op o)} -> option nat
let return (_, Dec x) = x

(** Returns true if 'd' matches with 'i' in tr.l*)
val matched : i:(nat * op) 
            -> d:(nat * op)
            -> tr:ae op
            -> Pure bool (requires (get_id i <> get_id d))
                        (ensures (fun b -> (Inc? (get_op i) /\ Dec? (get_op d) /\ mem i tr.l /\ mem d tr.l /\ 
                                        (return d) = Some (get_id i) /\ (tr.vis i d)) <==> (b = true)))
let matched i d tr = 
  (Inc? (get_op i) && Dec? (get_op d)) && (mem i tr.l && mem d tr.l) && (return d) = Some (get_id i) && (tr.vis i d)

val filter_uni : f:((nat * op) -> bool)
               -> l:list (nat * op) 
               -> Lemma (requires (unique_id l))
                       (ensures (unique_id (filter f l)))
                   [SMTPat (filter f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

(** Returns the list of decrement ops that matches 'i' *)
val dec_match_inc : tr:ae op 
                  -> i:(nat * op)
                  -> l:list(nat * op){(forall e. mem e l <==> mem e tr.l /\ Dec? (get_op e) /\ get_id i <> get_id e /\ 
                                    tr.vis i e /\ matched i e tr) /\ unique_id l /\ 
                                    ((exists d. mem d tr.l /\ get_id i <> get_id d /\ matched i d tr) <==> (length l > 0)) /\
                                    (length l > 0 <==> l <> [])}
let dec_match_inc tr i =
  filter (fun d -> get_id i <> get_id d && matched i d tr) tr.l

(** For each increment op there is atmost one matching decrement op.
    If a decrement operation returns an id, then there should be a matching increment op with that id in tr*)
assume val axiom : tr:ae op
                 -> Lemma (ensures (forall i. mem i tr.l /\ Inc? (get_op i) ==> length (dec_match_inc tr i) <= 1) /\
                                  (forall d id. mem d tr.l /\ Dec? (get_op d) /\ return d = Some id ==> 
                                    (exists i. mem i tr.l /\ Inc? (get_op i) /\ get_id i <> get_id d /\ tr.vis i d /\ get_id i = id)))

(** Returns the list of increment ops matched with decrement op*)
val match_inc : tr:ae op
              -> l:list(nat * op){(forall e. mem e l <==> mem e tr.l /\ Inc? (get_op e) /\ 
                         (exists d. mem d tr.l /\ Dec? (get_op d) /\ get_id e <> get_id d /\ matched e d tr)) /\ unique_id l}
let match_inc tr =
  filter (fun i -> mem i tr.l && Inc? (get_op i) && length (dec_match_inc tr i) > 0) tr.l

val remove : ele:(nat * op) 
           -> a:list(nat * op){unique_id a}
           -> Tot (b:list(nat * op) {unique_id b /\ (forall e. mem e b <==> mem e a /\ e <> ele) /\
                                  (mem ele a <==> List.Tot.length b = List.Tot.length a - 1) /\
                                  (not (mem ele a) <==> List.Tot.length b = List.Tot.length a)})
let rec remove ele a =
  match a with
  |[] -> []
  |x::xs -> if x = ele then xs else x::(remove ele xs)

(** Returns the list of unmatched increment op*)
val unmatch_inc : tr:ae op 
                -> Tot (l:list(nat * op){(forall e. mem e l <==> mem e tr.l /\ Inc? (get_op e) /\ 
                      (forall d. mem d tr.l /\ Dec? (get_op d) /\ get_id e <> get_id d ==> not (matched e d tr))) /\ unique_id l})
let unmatch_inc tr =
  filter (fun i -> Inc? (get_op i) && length (dec_match_inc tr i) = 0) tr.l

val lem_length : l:list(nat * op)
               -> l1:list(nat * op)
               -> Lemma (requires unique_id l1 /\ unique_id l)
                       (ensures (forall e. mem e l <==> mem e l1) ==> (length l = length l1))
                       (decreases %[l;l1])
let rec lem_length l l1 =
  match l, l1 with
  |[],[] -> ()
  |x::xs,_ -> lem_length xs (remove x l1)
  |[],_ -> ()

val lem_length1 : a:list (nat * op)
                -> b:list (nat * op)
                -> c:list (nat * op)
                -> Lemma (requires unique_id a /\ unique_id b /\ unique_id c)
                         (ensures (forall e. mem e a <==> mem e b \/ mem e c) /\
                                  (forall e. mem e b ==> not (mem e c)) ==> (length a = length b + length c))
                 (decreases %[a;b;c])
#set-options "--z3rlimit 1000"
let rec lem_length1 a b c =
  match a,b,c with
  |[],[],[] -> ()
  |x::xs,_,_ -> lem_length1 xs (remove x b) (remove x c)
  |[],x::xs,_ -> lem_length1 [] xs (remove x c)
  |[],[],_ -> ()

#set-options "--initial_fuel 7 --ifuel 7 --initial_ifuel 7 --fuel 7 --z3rlimit 10000"

val spec : o:(nat * op) -> tr:ae op -> rval
let spec o tr =
  match o with
  |(_, Inc) | (_, Dec _) -> Bot
  |(_, Rd) -> Val (length (unmatch_inc tr))

val sim : tr:ae op -> s0:s -> Tot (b:bool{b = true <==> s0 = length (unmatch_inc tr)})
let sim tr s0 =
  s0 = length (unmatch_inc tr)

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (a = b))
let convergence tr a b = ()

val pre_cond_prop_do : tr:ae op -> st:s -> op:(nat * op)
                     -> Tot (b:bool {b = true <==> (Dec? (get_op op) /\ st > 0 ==> length (unmatch_inc tr) > 0 /\ 
                                    (exists i. get_id i <> get_id op /\ matched i op tr)) /\
                                    (Dec? (get_op op) /\ st <= 0 ==> length (unmatch_inc tr) = 0 /\ return op = None)})

let pre_cond_prop_do tr st op =
  (if (Dec? (get_op op) && st > 0) then (length (unmatch_inc tr) > 0 && (existsb (fun i -> get_id i <> get_id op && matched i op tr) tr.l)) else true) &&
  (if (Dec? (get_op op) && st <= 0) then (length (unmatch_inc tr) = 0 && return op = None) else true)

val prop_do1 : tr:ae op
               -> st:s
               -> op:(nat * op)
               -> Lemma (requires (sim tr st) /\ not (mem_id (get_id op) tr.l) /\ get_id op > 0 /\
                                 (forall e. mem e tr.l ==> get_id e < get_id op) /\ Inc? (get_op op) /\
                                 pre_cond_prop_do tr st op)
                       (ensures (sim (abs_do tr op) (get_st (do st op))))
let prop_do1 tr st op =
  assert (dec_match_inc tr op = []); 
  assert (forall e. mem e (unmatch_inc (abs_do tr op)) <==> mem e (unmatch_inc tr) \/ e = op);
  lem_length1 (unmatch_inc (abs_do tr op)) (unmatch_inc tr) [op]

val prop_do2 : tr:ae op
               -> st:s
               -> op:(nat * op)
               -> Lemma (requires (sim tr st) /\ not (mem_id (get_id op) tr.l) /\ get_id op > 0 /\
                                 (forall e. mem e tr.l ==> get_id e < get_id op) /\ Dec? (get_op op) /\
                                 pre_cond_prop_do tr st op)
                       (ensures (sim (abs_do tr op) (get_st (do st op))))
let prop_do2 tr st op = ()

val prop_do3 : tr:ae op
               -> st:s
               -> op:(nat * op)
               -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\ get_id op > 0 /\
                                 (forall e. mem e tr.l ==> get_id e < get_id op) /\ Rd? (get_op op))
                        (ensures (sim (abs_do tr op) (get_st (do st op))))
let prop_do3 tr st op =
  assert (forall e. mem e (unmatch_inc tr) <==> mem e (unmatch_inc (abs_do tr op)));
  lem_length (unmatch_inc tr) (unmatch_inc (abs_do tr op))

val prop_do : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ not (mem_id (get_id op) tr.l) /\ get_id op > 0 /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ pre_cond_do tr st /\
                                pre_cond_prop_do tr st op)
                      (ensures (sim (abs_do tr op) (get_st (do st op))))
let prop_do tr st op = 
  match get_op op with
  |Inc -> prop_do1 tr st op
  |Dec _ -> prop_do2 tr st op
  |Rd -> prop_do3 tr st op

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (get_rval (do st op) = spec op tr))
let prop_spec tr st op = ()

val merge : l:s -> a:s -> b:s
          -> Pure s
            (requires true)
            (ensures (fun r -> (((a >= l \/ b >= l) \/ (a + b > l)) <==> r = a + b - l) /\
                            ((a < l /\ b < l) /\ a + b <= l) ==> r = 0))
let merge l a b =
  if ((a >= l || b >= l) || (a + b > l)) then a + b - l else 0

(** Returns the list of unmatched increment ops in l which are matched by decrement ops in a*)
val match_ltr_atr : l:ae op -> a:ae op
                  -> Pure (list (nat * op))
                         (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                         (ensures (fun r -> (forall e. mem e r <==> mem e (unmatch_inc l) /\ Inc? (get_op e) /\
                                     (exists d. get_id e <> get_id d && matched e d (union l a))) /\ unique_id r /\
                                     (length r = length (filter (fun i -> Inc? (get_op i) && 
                                     (dec_match_inc (union l a) i) <> [] && 
                                     length (dec_match_inc (union l a) i) > 0) (unmatch_inc l)))))
let match_ltr_atr l a =
  filter (fun i -> Inc? (get_op i) && dec_match_inc (union l a) i <> [] && length (dec_match_inc (union l a) i) > 0) (unmatch_inc l)

val length_union : l:list(nat * op)
                 -> a:list(nat * op)
                 -> la:list(nat * op)
                 -> Lemma (requires unique_id l /\ unique_id a /\ unique_id la /\
                                   (forall e. mem e l ==> not (mem_id (get_id e) a)) /\
                                   (forall e. mem e la ==> mem e l) /\
                                   (forall e. mem e (union1 l a) <==> ((mem e a \/ mem e l) /\ not (mem e la))))
                         (ensures (length (union1 l a) = length a + length l - length la))
                         (decreases %[l;a;la])
let rec length_union l a la =
  match l,a,la with
  |[],[],[] -> ()
  |x::xs,_,_ -> length_union xs a la
  |[],x::xs,_ -> length_union l xs la
  |[],[],_ -> ()

val lem_union : l:ae op
               -> a:ae op
               -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                       (ensures (forall e. mem e (unmatch_inc (union l a)) <==> mem e (union1 (unmatch_inc l) (unmatch_inc a))))
                       (decreases %[l.l;a.l])
let rec lem_union l a =
  match l.l,a.l with
  |[],[] -> ()
  |x::xs,_ -> lem_union (A l.vis xs) a
  |[],x::xs -> lem_union l (A a.vis xs)

val unmatch_union : l:ae op
              -> a:ae op
              -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                      (ensures (forall e. mem e (unmatch_inc (union l a)) <==> 
                                  ((mem e (unmatch_inc a) \/ mem e (unmatch_inc l)) /\ not (mem e (match_ltr_atr l a)))) /\
                               (length (unmatch_inc (union l a)) = 
                                  length (unmatch_inc a) + length (unmatch_inc l) - length (match_ltr_atr l a)))
let unmatch_union l a = 
  lem_union l a; 
  lem_length (unmatch_inc (union l a)) (union1 (unmatch_inc l) (unmatch_inc a));
  length_union (unmatch_inc l) (unmatch_inc a) (match_ltr_atr l a)

val length_absmerge : l:list(nat * op)
                    -> a:list(nat * op)
                    -> b:list(nat * op)
                    -> la:list(nat * op)
                    -> lb:list(nat * op)
                    -> Lemma (requires unique_id l /\ unique_id a /\ unique_id la /\ unique_id b /\ unique_id lb /\
                                     (forall e. mem e l ==> not (mem_id (get_id e) a)) /\
                                     (forall e. mem e a ==> not (mem_id (get_id e) b)) /\
                                     (forall e. mem e l ==> not (mem_id (get_id e) b)) /\
                                     (forall e. mem e la ==> mem e l) /\ (forall e. mem e lb ==> mem e l) /\
                                     (forall e. mem e la ==> not (mem e lb)) /\
                      (forall e. mem e (abs_merge1 l a b) <==> ((mem e a \/ mem e b \/ mem e l) /\ not (mem e la) /\ not (mem e lb))))
                         (ensures (length (abs_merge1 l a b) = length a + length b + length l - length la - length lb))
                         (decreases %[l;a;b;la;lb])
let rec length_absmerge l a b la lb =
  match l,a,b,la,lb with
  |[],[],[],[],[] -> ()
  |x::xs,_,_,_,_ -> length_absmerge xs a b la lb
  |[],x::xs,_,_,_ -> length_absmerge l xs b la lb
  |[],[],x::xs,_,_ -> length_absmerge l a xs la lb
  |[],[],[],x::xs,_ -> length_absmerge l a b xs lb
  |[],[],[],[],x::xs -> length_absmerge l a b la xs

val unmatch_absmerge : l:ae op
                     -> a:ae op
                     -> b:ae op
                     -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                                       (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                                       (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)) /\
                                       (forall e. mem e (match_ltr_atr l a) ==> not (mem e (match_ltr_atr l b))))
                             (ensures (forall e. mem e (unmatch_inc (abs_merge l a b)) <==> 
                             ((mem e (unmatch_inc a) \/ mem e (unmatch_inc b) \/ mem e (unmatch_inc l)) /\
                               not (mem e (match_ltr_atr l a)) /\ not (mem e (match_ltr_atr l b)))) /\
                        (length (unmatch_inc (abs_merge l a b)) = 
                                      length (unmatch_inc a) + length (unmatch_inc b) + length (unmatch_inc l) 
                                      - length (match_ltr_atr l a) - length (match_ltr_atr l b)))
let unmatch_absmerge l a b = 
  lem_union l a; lem_union l b; 
  lem_length (unmatch_inc (union l a)) (union1 (unmatch_inc l) (unmatch_inc a)); 
  lem_length (unmatch_inc (union l b)) (union1 (unmatch_inc l) (unmatch_inc b));
  lem_length (unmatch_inc (abs_merge l a b)) (abs_merge1 (unmatch_inc l) (unmatch_inc a) (unmatch_inc b)); 
  length_union (unmatch_inc l) (unmatch_inc a) (match_ltr_atr l a);
  length_union (unmatch_inc l) (unmatch_inc b) (match_ltr_atr l b);
  length_absmerge (unmatch_inc l) (unmatch_inc a) (unmatch_inc b) (match_ltr_atr l a) (match_ltr_atr l b); ()

let pre_cond_merge l a b = true
let pre_cond_prop_merge ltr l atr a btr b = true

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
                       (ensures (sim (abs_merge ltr atr btr) (merge l a b)))
let prop_merge ltr l atr a btr b = 
  unmatch_union ltr atr;
  unmatch_union ltr btr;
  unmatch_absmerge ltr atr btr

instance nn_ctr : mrdt s op rval = {
  Library.init = init;
  Library.spec = spec;
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
