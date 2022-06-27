module Ew
open FStar.List.Tot

open Library

type s = nat * bool

type rval = |Val : s -> rval
            |Bot

type op = 
  |Enable
  |Disable
  |Rd

val ope : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id. op1 = (id,Enable))})
let ope op1 =
  match op1 with
  |(id,Enable) -> true
  |_ -> false

val opd : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id. op1 = (id,Disable))})
let opd op1 = 
  match op1 with
  |(id,Disable) -> true
  |_ -> false

val opr : op1:(nat * op) -> Tot (b:bool {b=true <==> (exists id. op1 = (id,Rd))})
let opr op1 = not (ope op1 || opd op1)

val init : nat * bool
let init = (0, false)

let pre_cond_op s1 op = true

val app_op : s1:s -> op:(nat * op) -> Tot (s2:(s * rval) {(ope op ==> s2 = ((fst s1 + 1, true), Bot)) /\
                                                      (opd op ==> s2 = ((fst s1, false), Bot)) /\
                                                      (opr op ==> s2 = (s1, Val s1))})
let app_op (c,f) e = 
  match e with
  |(_,Enable) -> ((c + 1, true), Bot)
  |(_,Disable) -> ((c, false), Bot)
  |(_,Rd) -> ((c,f), Val (c,f))

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

val spec : (nat * op) -> ae op -> rval
let spec o tr = 
  match o with
  |(_,Enable) -> Bot
  |(_,Disable) -> Bot
  |(_,Rd) -> Val (sum tr.l, flag tr)

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> ((fst s1 = sum tr.l) /\ (snd s1 = flag tr))})
let sim tr s1 = (s1 = (sum tr.l, flag tr))

val lemma1 : l:ae op
           -> a:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                   (ensures (forall e. mem e (union1 l a) <==> mem e l.l \/ mem e a.l) /\
                            (sum (union l a).l = sum l.l + sum a.l))
                            (decreases %[l.l;a.l])
                            [SMTPat (sum (union l a).l)]
#set-options "--z3rlimit 1000000"
let rec lemma1  l a =
  match l,a with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma1 (A l.vis xs) a
  |(A _ []), (A _ (x::xs)) -> lemma1 l (A a.vis xs)

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

val pre_cond_merge1 : s -> s -> s -> bool
let pre_cond_merge1 l a b = fst a >= fst l && fst b >= fst l

let pre_cond_merge ltr l atr a btr b = true

val merge1 : l:s
           -> a:s
           -> b:s
           -> Pure s
             (requires pre_cond_merge1 l a b)
             (ensures (fun res -> (snd res = true <==> (snd a = true /\ snd b = true) \/ 
                                                  (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                                  (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                               (snd res = false <==> (snd a = false /\ snd b = false) \/
                                                   (snd a = true /\ snd b = false /\ fst a = fst l) \/ 
                                                   (snd b = true /\ snd a = false /\ fst b = fst l)) /\
                               (fst res = fst a + fst b - fst l)))
let merge1 l a b =
  let c = fst a + fst b - fst l in
  let f = merge_flag l a b in
  c, f

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (fun res -> (snd res = true <==> (snd a = true /\ snd b = true) \/ 
                                                        (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                                        (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                                     (snd res = false <==> (snd a = false /\ snd b = false) \/
                                                         (snd a = true /\ snd b = false /\ fst a = fst l) \/ 
                                                         (snd b = true /\ snd a = false /\ fst b = fst l)) /\
                                     (fst res = fst a + fst b - fst l) /\
                                     (res = merge1 l a b))) 
#set-options "--z3rlimit 10000"
let merge ltr l atr a btr b = 
  lemma1 ltr atr; 
  lemma1 ltr btr;
  let c = fst a + fst b - fst l in
  let f = merge_flag l a b in
  c, f

val lemma2 : l:ae op
           -> a:ae op
           -> b:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                             (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))
                   (ensures (forall e. mem e (absmerge1 l a b) <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                            (sum (absmerge l a b).l = sum a.l + sum b.l + sum l.l))
                            (decreases %[l.l;a.l;b.l])
                            [SMTPat (sum (absmerge l a b).l)]
let rec lemma2 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma2 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma2 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma2 l a (A b.vis xs)

val lem_sum : l:list (nat * op)
            -> Lemma (requires (unique_id l))
                    (ensures (sum l > 0 <==> (exists e. mem e l /\ get_op e = Enable)) /\
                             (sum l = 0 <==> ((forall e. mem e l ==> (get_op e = Disable \/ get_op e = Rd) /\ l <> []) \/ l = [])))
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
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma1 ltr atr;
  lemma1 ltr btr;
  lemma2 ltr atr btr;
  lem_sum atr.l;
  lem_sum btr.l;
  ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (sim (append tr op) (get_st (app_op st op))))
let prop_oper tr st op = ()

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
                      (ensures (get_rval (app_op st op) = spec op tr))
let prop_spec tr st op = ()

instance ew : mrdt s op rval = {
  Library.init = init;
  Library.spec = spec;
  Library.sim = sim;
  Library.pre_cond_op = pre_cond_op;
  Library.app_op = app_op;
  Library.prop_oper = prop_oper;
  Library.pre_cond_merge1 = pre_cond_merge1;
  Library.pre_cond_merge = pre_cond_merge;
  Library.merge1 = merge1;
  Library.merge = merge;
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
                   (ensures (snd a = true /\ snd b = false /\ fst a = fst l ==> flag (absmerge ltr atr btr) = false) /\
                            (snd b = true /\ snd a = false /\ fst b = fst l ==> flag (absmerge ltr atr btr) = false))

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
                   (ensures (snd a = true /\ snd b = false /\ fst a > fst l ==> flag (absmerge ltr atr btr) = true) /\
                            (snd b = true /\ snd a = false /\ fst b > fst l ==> flag (absmerge ltr atr btr) = true))

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
                   (ensures (snd a = true /\ snd b = true ==> flag (absmerge ltr atr btr) = true) /\
                            (snd a = false /\ snd b = false ==> flag (absmerge ltr atr btr) = false))

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
                   (ensures (sum (absmerge ltr atr btr).l = fst (merge ltr l atr a btr b)))

#set-options "--z3rlimit 1000000"
let lemma0 ltr l atr a btr b = 
  lemma1 ltr atr; 
  lemma1 ltr btr;
  lemma2 ltr atr btr; ()
*)
