module Ew
open FStar.List.Tot

open Library
type s = nat * bool

type op = 
  |Add 
  |Rem

val opa : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id. op1 = (id,Add))})
let opa op1 =
    match op1 with
    |(id,Add) -> true
    |_ -> false

val opr : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id. op1 = (id,Rem))})
let opr op1 =
      match op1 with
      |(id,Rem) -> true
      |_ -> false

val fst : s1:s -> Tot (n:nat {exists f. s1 = (n,f)})
let fst (c,f) = c

val snd : s1:s -> Tot (b:bool {exists c. s1 = (c,b)})
let snd (c,f) = f

val app_op : s1:s -> op:(nat * op) -> Tot (s2:s {opa op ==> (fst s2 = fst s1 + 1 /\ snd s2 = true) /\
                                             opr op ==> (fst s2 = fst s1 /\ snd s2 = false)})
let app_op (c,f) e = 
      match e with
      |(_,Add) -> (c + 1, true)
      |(_,Rem) -> (c, false)

instance ew : datatype s op = {
  Library.app_op = app_op
}

val sum : l:(list (nat * op))
        -> Tot (n:nat {n = (List.Tot.length (filter (fun a -> get_op a = Add) l))}) (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_, Add)::xs -> sum xs + 1
  |(_, Rem)::xs -> sum xs

val flag : tr:ae op
         -> Tot (b:bool {((b = true) <==> ((exists e. (mem e tr.l /\ get_op e = Add /\ 
                                       (forall d. (mem d tr.l /\ get_id e <> get_id d /\ get_op d = Rem) ==> not (tr.vis e d)))))) /\
                       ((b = false) <==> ((forall e. (mem e tr.l /\ get_op e = Add ==> 
                                        (exists d. mem d tr.l /\ get_id e <> get_id d /\ get_op d = Rem /\ tr.vis e d))) \/ (forall d. mem d tr.l ==> get_op d = Rem) \/ tr.l = []))})

let flag tr = if ((forallb (fun e -> (existsb (fun d -> (get_op d = Rem) && get_id e <> get_id d && tr.vis e d) tr.l))
                                  (filter (fun e -> (get_op e = Add)) tr.l))
                 || (forallb (fun d -> (get_op d = Rem)) tr.l)
                 || tr.l = []) then false else true

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> ((fst s1 = sum tr.l) /\ (snd s1 = flag tr))})
let sim tr s1 = (s1 = (sum tr.l, flag tr))

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))
let prop_oper tr st op = ()

val lemma1 : l:ae op
           -> a:ae op
           -> Lemma
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)))
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

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                             (ensures (fun res -> (snd res = true <==> (snd a = true /\ snd b = true) \/ 
                                                           (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                                           (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                                           (snd res = false <==> (snd a = false /\ snd b = false) \/
                                                            (snd a = true /\ snd b = false /\ fst a = fst l) \/ 
                                                            (snd b = true /\ snd a = false /\ fst b = fst l)))) 
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
           -> Lemma (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                             (forall e. mem e l.l ==> not (member (get_id e) b.l)))
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
             -> Lemma (requires (unique l))
                      (ensures (sum l > 0 <==> (exists e. mem e l /\ get_op e = Add)) /\
                               (sum l = 0 <==> ((forall e. mem e l ==> get_op e = Rem /\ l <> []) \/ l = []))) (decreases l)
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
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
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

val convergence : tr:ae op
                 -> a:s
                 -> b:s
                 -> Lemma (requires (sim tr a /\ sim tr b))
                         (ensures a = b)
                         [SMTPat (sim tr a /\ sim tr b)]
let convergence tr a b = ()

instance _ : mrdt s op ew = {
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence;
  Library.sim = sim;
  Library.prop_oper = prop_oper
}

