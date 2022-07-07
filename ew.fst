module Ew
open FStar.List.Tot

#set-options "--query_stats"

open Library

type s = nat * bool

type rval = |Val : bool -> rval
            |Bot

type op = 
  |Enable
  |Disable
  |Rd

val init : nat * bool
let init = (0, false)

let pre_cond_do s1 op = true
let pre_cond_prop_do tr s1 op = true

val do : s1:s -> o:(nat * op) -> Tot (s2:(s * rval) {(get_op o = Enable ==> s2 = ((fst s1 + 1, true), Bot)) /\
                                                 (get_op o = Disable ==> s2 = ((fst s1, false), Bot)) /\
                                                 (get_op o = Rd ==> s2 = (s1, Val (snd s1)))})
let do (c,f) e = 
  match e with
  |(_,Enable) -> ((c + 1, true), Bot)
  |(_,Disable) -> ((c, false), Bot)
  |(_,Rd) -> ((c,f), Val f)

val sum : l:(list (nat * op))
        -> Tot (n:nat {n = (List.Tot.length (filter (fun a -> get_op a = Enable) l))}) (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_, Enable)::xs -> sum xs + 1
  |_::xs -> sum xs

val flag : tr:ae op
         -> Tot (b:bool {((b = true) <==> ((exists e. (mem e tr.l /\ get_op e = Enable /\ 
                                       (forall d. (mem d tr.l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not (tr.vis e d)))))) /\
                       ((b = false) <==> ((forall e. (mem e tr.l /\ get_op e = Enable ==> 
                                        (exists d. mem d tr.l /\ get_id e <> get_id d /\ get_op d = Disable /\ tr.vis e d))) \/ 
                                        (forall d. mem d tr.l ==> get_op d = Disable \/ get_op d = Rd) \/ tr.l = []))})

let flag tr = if ((forallb (fun e -> (existsb (fun d -> (get_op d = Disable) && get_id e <> get_id d && tr.vis e d) tr.l))
                                  (filter (fun e -> (get_op e = Enable)) tr.l))
                 || (forallb (fun d -> (get_op d = Disable || get_op d = Rd)) tr.l)
                 || tr.l = []) then false else true

val spec : o:(nat * op) -> tr:ae op -> rval
let spec o tr = 
  match o with
  |(_,Enable) -> Bot
  |(_,Disable) -> Bot
  |(_,Rd) -> Val (flag tr)

val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> ((fst s1 = sum tr.l) /\ (snd s1 = flag tr))})
let sim tr s1 = (s1 = (sum tr.l, flag tr))

val lemma11 : l:list(nat * op) {unique_id l}
            -> a:list(nat * op) {unique_id a}
            -> Lemma (requires (forall e. mem e l ==> not (mem_id (get_id e) a)))
                    (ensures (sum (union1 l a) = sum l + sum a))
let rec lemma11 l a =
  match l,a with
  |[],[] -> ()
  |x::xs,_ -> lemma11 xs a
  |[],_ -> ()

val lemma1 : l:ae op
           -> a:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                   (ensures (forall e. mem e (union l a).l <==> mem e l.l \/ mem e a.l) /\
                            (sum (union l a).l = sum l.l + sum a.l))
let lemma1 l a = lemma11 l.l a.l

val merge_flag : l:s 
               -> a:s{fst a >= fst l}
               -> b:s{fst b >= fst l}
               -> Tot (b1:bool {(b1 = true <==> (snd a = true /\ snd b = true) \/ 
                                             (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                             (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                               (b1 = false <==> (snd a = false /\ snd b = false) \/ 
                                              (snd a = true /\ snd b = false /\ fst a = fst l) \/
                                              (snd b = true /\ snd a = false /\ fst b = fst l))}) 
let merge_flag l a b =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
  if af && bf then true
    else if not af && not bf then false
      else if af then ac - lc > 0
        else bc - lc > 0

val pre_cond_merge : s -> s -> s -> bool
let pre_cond_merge l a b = fst a >= fst l && fst b >= fst l

let pre_cond_prop_merge ltr l atr a btr b = true

val merge : l:s
          -> a:s
          -> b:s
          -> Pure s
            (requires pre_cond_merge l a b)
            (ensures (fun res -> (snd res = true <==> (snd a = true /\ snd b = true) \/ 
                                                 (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                                 (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                              (snd res = false <==> (snd a = false /\ snd b = false) \/
                                                  (snd a = true /\ snd b = false /\ fst a = fst l) \/ 
                                                  (snd b = true /\ snd a = false /\ fst b = fst l)) /\
                              (fst res = fst a + fst b - fst l)))
let merge l a b =
  let c = fst a + fst b - fst l in
  let f = merge_flag l a b in
  c, f

val lemma21 : l:list(nat * op) {unique_id l}
            -> a:list(nat * op) {unique_id a}
            -> b:list(nat * op) {unique_id b}
            -> Lemma (requires (forall e. mem e l ==> not (mem_id (get_id e) a)) /\
                              (forall e. mem e a ==> not (mem_id (get_id e) b)) /\
                              (forall e. mem e l ==> not (mem_id (get_id e) b)))
                    (ensures (forall e. mem e (abs_merge1 l a b) <==> mem e l \/ mem e a \/ mem e b) /\
                             (sum (abs_merge1 l a b) = sum a + sum b + sum l))
                             (decreases %[l;a;b])
#set-options "--z3rlimit 1000"
let rec lemma21 l a b =
  match l,a,b with
  |[],[],[] -> ()
  |x::xs,_,_ -> lemma21 xs a b
  |[],x::xs,_ -> lemma21 [] xs b
  |[],[],_ -> ()

val lemma2 : l:ae op
           -> a:ae op
           -> b:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                             (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))
                   (ensures (forall e. mem e (abs_merge l a b).l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                            (sum (abs_merge l a b).l = sum a.l + sum b.l + sum l.l))
let lemma2 l a b = lemma21 l.l a.l b.l

val lem_sum : l:list (nat * op)
            -> Lemma (requires (unique_id l))
                    (ensures (sum l > 0 <==> (exists e. mem e l /\ get_op e = Enable)) /\
                             (sum l = 0 <==> ((forall e. mem e l ==> 
                                    (get_op e = Disable \/ get_op e = Rd) /\ l <> []) \/ l = [])))
                             (decreases l)
let rec lem_sum l = 
  match l with
  |[] -> ()
  |x::xs -> lem_sum xs

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

#set-options "--z3rlimit 100000"
let prop_merge ltr l atr a btr b = 
  lemma1 ltr atr;
  lemma1 ltr btr;
  lemma2 ltr atr btr;
  lem_sum atr.l;
  lem_sum btr.l;
  ()

val prop_do : tr:ae op
            -> st:s
            -> op:(nat * op)
            -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                              (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                    (ensures (sim (abs_do tr op) (get_st (do st op))))
let prop_do tr st op = ()

val convergence : tr:ae op
                 -> a:s
                 -> b:s
                 -> Lemma (requires (sim tr a /\ sim tr b))
                         (ensures a = b)
let convergence tr a b = ()

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (get_rval (do st op) = spec op tr))
let prop_spec tr st op = ()

instance ew : mrdt s op rval = {
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


(* Additional lemmas for prop_merge 

val lemma4 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> a:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (snd a = true /\ snd b = false /\ fst a = fst l ==> flag (abs_merge ltr atr btr) = false) /\
                            (snd b = true /\ snd a = false /\ fst b = fst l ==> flag (abs_merge ltr atr btr) = false))

#set-options "--z3rlimit 1000000"
let lemma4 ltr l atr a btr b = 
  lemma1 ltr atr; lemma1 ltr btr;
  lem_sum atr.l; lem_sum btr.l;
  ()

val lemma5 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> a:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (snd a = true /\ snd b = false /\ fst a > fst l ==> flag (abs_merge ltr atr btr) = true) /\
                            (snd b = true /\ snd a = false /\ fst b > fst l ==> flag (abs_merge ltr atr btr) = true))

#set-options "--z3rlimit 1000000"
let lemma5 ltr l atr a btr b = 
  lemma1 ltr atr; lemma1 ltr btr;
  lem_sum atr.l; lem_sum btr.l;
  ()

val lemma3 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> a:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (snd a = true /\ snd b = true ==> flag (abs_merge ltr atr btr) = true) /\
                            (snd a = false /\ snd b = false ==> flag (abs_merge ltr atr btr) = false))

#set-options "--z3rlimit 1000000"
let lemma3 ltr l atr a btr b = ()

val lemma0 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> a:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (sum (abs_merge ltr atr btr).l = fst (merge ltr l atr a btr b)))

#set-options "--z3rlimit 1000000"
let lemma0 ltr l atr a btr b = 
  lemma1 ltr atr; 
  lemma1 ltr btr;
  lemma2 ltr atr btr; ()
*)
