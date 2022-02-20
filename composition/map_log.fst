module Map_log
open FStar.List.Tot

open Library
module C = Log

type op = (string (*channel name*) * C.op)

val get_ch : op1:(nat * op) -> Tot (s:string {exists id m. op1 = (id, (s, C.Append m))})
let get_ch (id, (ch, C.Append m)) = ch

val get_log : op1:(nat * op) -> Tot (l:C.op {exists id ch. op1 = (id, (ch, l))})
let get_log (id, (ch, C.Append m)) = (C.Append m)

val get_msg : op1:(nat * op) -> Tot (m:string {exists id ch. op1 = (id, (ch, C.Append m))})
let get_msg (id, (ch, C.Append m)) = m

val get_ch_s : s:(string * C.s) -> Tot (s1:string {(exists c. s = (s1,c))})
let get_ch_s (i,_) = i

val mem_ch_s : ele1:string
             -> l:list (string * C.s)
             -> Tot (b:bool {b=true <==> (exists c. mem (ele1,c) l) /\ (exists e. mem e l /\ get_ch_s e = ele1)})
let rec mem_ch_s ele1 l =
  match l with
  |[] -> false
  |x::xs -> get_ch_s x = ele1 || mem_ch_s ele1 xs

val unique_ch : list (string * C.s) -> bool
let rec unique_ch l =
  match l with
  |[] -> true
  |(ele,_)::xs -> not (mem_ch_s ele xs) && unique_ch xs

val get_msg_s1 : s:(string * C.s) -> Tot (c:C.s {(exists i. s = (i,c))})
let get_msg_s1 (_, c) = c

type s = l:list (string * C.s) {unique_ch l}

val get_msg_s : i:string -> s1:s -> Tot (c:C.s {(mem_ch_s i s1 ==> mem (i,c) s1 /\ (exists e. mem e s1 ==> e = (i,c))) /\ 
                                       (not (mem_ch_s i s1) ==> c = [])})
let rec get_msg_s i s1 =
  match s1 with
  |[] -> []
  |x::xs -> if get_ch_s x = i then (get_msg_s1 x) else get_msg_s i xs

val lemma2 : s1:s 
           -> Lemma (requires true)
                   (ensures (forall e. mem e s1 ==> (get_msg_s (get_ch_s e) s1 = get_msg_s1 e)) /\
                            (forall e. mem e s1 ==> C.unique_s (get_msg_s (get_ch_s e) s1) /\
                                              C.total_order (get_msg_s (get_ch_s e) s1)))
                [SMTPat (forall e. mem e s1)]
#set-options "--z3rlimit 10000000"
let rec lemma2  s1 = 
      match s1 with
      |[] -> ()
      |x::xs -> lemma2 xs 

val mem_op : ele1:op
           -> l:list (nat * op)
           -> Tot (b:bool {b=true <==> (exists id. mem (id, ele1) l) })
let rec mem_op ele2 l =
  match l with
  |[] -> false
  |(_, ele1)::xs -> ele1 = ele2 || mem_op ele2 xs

val mem_ch : i:string -> l:list (nat * op) -> Tot (b:bool {b=true <==> (exists id op. mem (id, (i, op)) l)})
let rec mem_ch ele2 l =
    match l with
    |[] -> false
    |(_, (ele1, _))::xs -> ele1 = ele2 || mem_ch ele2 xs

val filter_uni : #op:eqtype 
               -> f:((nat * op) -> bool)
               -> l:list (nat * op) 
               -> Lemma (requires (unique l ))
                       (ensures (unique (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni #op f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val project_op : o1:(nat * op)
               -> Tot (o2:(nat * C.op) {o2 = (get_id o1, get_log o1)})
let project_op op =
    match op with
    |(id, (ch, log)) -> (id, log)

val project1 : i:string 
             -> l:ae op
             -> Pure (list (nat * C.op))
                    (requires true)
                    (ensures (fun r -> (forall id. member id r <==> member id l.l /\ 
                                    get_op (get_eve id l.l) = (i, (C.Append (get_msg (get_eve id l.l))))) /\
                                  (forall id. member id r <==> (member id l.l /\ get_ch (get_eve id l.l) = i)) /\ unique r /\
                (forall e. mem e r <==> (mem ((get_id e), (i, C.Append (C.get_msg e))) l.l)) /\
                (forall e. mem e l.l /\ get_ch e = i ==> mem (project_op e) r)))
            (decreases List.Tot.length l.l)

#set-options "--z3rlimit 10000000"
let rec project1 i l =
  match l.l with
  |[] -> []
  |x::xs -> if (get_ch x = i) then (project_op x)::project1 i (A l.vis xs) else (project1 i (A l.vis xs))

val project : i:string
            -> l:ae op
            -> Pure (ae C.op)
                   (requires true)
                   (ensures (fun r -> (forall id. member id r.l <==> member id l.l /\ 
                                   get_op (get_eve id l.l) = (i, (C.Append (get_msg (get_eve id l.l))))) /\
              (forall id. member id r.l <==> (member id l.l /\ get_ch (get_eve id l.l) = i)) /\ unique r.l /\
                 (forall e. mem e r.l <==> (mem ((get_id e), (i, C.Append (C.get_msg e))) l.l)) /\
                 (forall e. mem e l.l /\ get_ch e = i ==> mem (project_op e) r.l) /\
                 (forall e e1. (get_id e <> get_id e1 /\ mem (get_id e, (i, C.Append (C.get_msg e))) l.l /\ 
              mem (get_id e1, (i, C.Append (C.get_msg e1))) l.l /\
                  l.vis (get_id e, (i, C.Append (C.get_msg e))) (get_id e1, (i, C.Append (C.get_msg e1)))) <==> 
            (get_id e <> get_id e1 /\ mem e r.l /\ mem e1 r.l /\ r.vis e e1))))
               (decreases length l.l)

#set-options "--z3rlimit 10000000"
let project i l =
              (A (fun o o1 -> (mem (get_id o, (i, C.Append (C.get_msg o))) l.l && mem (get_id o1, (i, C.Append (C.get_msg o1))) l.l &&  get_id o <> get_id o1 && l.vis (get_id o, (i, C.Append (C.get_msg o))) (get_id o1, (i, C.Append (C.get_msg o1))))) (project1 i l))

val app_op : st:s -> op1:(nat * op)
           -> Pure s 
             (requires (exists id ch m. op1 = (id, (ch, (C.Append m)))) /\
                       (mem_ch_s (get_ch op1) st ==> 
                               (forall id. C.mem_id_s id (get_msg_s (get_ch op1) st) ==> get_id op1 > id)))
             (ensures (fun r -> (forall ch. mem_ch_s ch r <==> mem_ch_s ch st \/ ch = get_ch op1) /\
                             (forall id. C.mem_id_s id (get_msg_s (get_ch op1) r) <==>
                                       C.mem_id_s id (get_msg_s (get_ch op1) st) \/ id = get_id op1) /\
                             (forall ch. mem_ch_s ch r /\ ch <> get_ch op1 ==>
                                    (get_msg_s ch st) = (get_msg_s ch r) /\
                                    (forall e. mem e (get_msg_s ch st) <==> mem e (get_msg_s ch r))) /\
                             (get_msg_s (get_ch op1) r) = (get_id op1, get_msg op1)::(get_msg_s (get_ch op1) st) /\
                                                (forall e. mem e (get_msg_s (get_ch op1) r) <==> mem e (get_msg_s (get_ch op1) st) \/ e = (get_id op1, get_msg op1))))

#set-options "--z3rlimit 10000000"
let rec app_op st op1 =
  match st with
  |[] -> [(get_ch op1, [(get_id op1, get_msg op1)])]
  |(ch, x)::xs -> if ch = get_ch op1 then
                         (ch, ((get_id op1, get_msg op1)::x))::xs
                else (ch, x)::app_op xs op1

(*)instance orset : datatype s op = {
  Library.app_op = app_op
}*)

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {(b = true) <==> (forall ch. mem_ch_s ch s1 <==> mem_ch ch tr.l) /\
                                     (forall ch. mem_ch_s ch s1 ==> C.sim (project ch tr) (get_msg_s ch s1)) /\
                                     (forall e. mem e tr.l ==> (exists e1. mem e1 s1 ==> get_ch e = get_ch_s e1 /\
                                           mem (get_id e, get_msg e) (get_msg_s1 e1)))})

#set-options "--z3rlimit 10000000"
let sim tr s1 = 
  forallb (fun e -> mem_ch (get_ch_s e) tr.l) s1 &&
  forallb (fun e -> mem_ch_s (get_ch e) s1) tr.l &&
  forallb (fun e -> C.sim (project (get_ch_s e) tr) (get_msg_s (get_ch_s e) s1)) s1 &&
  forallb (fun e -> (existsb (fun e1 -> get_ch e = get_ch_s e1 && mem (get_id e, get_msg e) (get_msg_s1 e1)) s1)) tr.l

val lemma3 : tr:ae op -> s1:s
           -> Lemma (requires (sim tr s1))
                   (ensures (forall ch e1. mem_ch_s ch s1 /\ mem e1 (get_msg_s ch s1) ==>
                                      mem (get_id e1, (ch, (C.Append (C.snd e1)))) tr.l) /\
                                      (forall ch m. not (mem_ch_s ch s1) ==> (forall e. mem e tr.l ==> get_op e <> (ch, m))))
                               [SMTPat (sim tr s1)]
let lemma3 tr s1 = ()

val lemma4 : tr:ae op -> s1:s
           -> Lemma (requires sim tr s1)
                   (ensures (forall i. (C.sim (project i tr) (get_msg_s i s1))))
                      [SMTPat (sim tr s1)]
let lemma4 tr s1 = ()

val convergence1 : tr:ae op
                 -> a:s
                 -> b:s
                 -> Lemma (requires (sim tr a /\ sim tr b))
                         (ensures (forall e. mem_ch_s e a <==> mem_ch_s e b))
#set-options "--z3rlimit 100000000"
let convergence1 tr a b = ()

val unique_chs : list string -> Tot bool
      let rec unique_chs l =
      match l with
      |[] -> true
      |x::xs -> not (mem x xs) && unique_chs xs

val get_lst : m:s -> Pure (list string)
                           (requires true)
                           (ensures (fun r -> (forall i. mem i r <==> mem_ch_s i m) /\ unique_chs r))
let rec get_lst m =
          match m with
          |[] -> []
          |(i,x)::xs -> i::get_lst xs

val convergence2 : tr:ae op
                 -> a:s
                 -> b:s
                 -> Lemma (requires (sim tr a /\ sim tr b))
                         (ensures (forall ch. mem_ch_s ch a /\ mem_ch_s ch b ==> 
                                  (forall e e1. mem e (get_msg_s ch a) /\ mem e1 (get_msg_s ch a) /\ 
                                  C.fst e <> C.fst e1 /\ C.fst e > C.fst e1 /\ C.ord e e1 (get_msg_s ch a)  <==> 
                                   mem e (get_msg_s ch b) /\ mem e1 (get_msg_s ch b) /\ C.fst e <> C.fst e1 /\
                                   C.fst e > C.fst e1 /\ C.ord e e1 (get_msg_s ch b))) /\
                                  (forall ch. mem_ch_s ch a /\ mem_ch_s ch b ==>
                                  (forall e. C.mem_id_s e (get_msg_s ch a) <==> C.mem_id_s e (get_msg_s ch b))))

#set-options "--z3rlimit 100000000"
let convergence2 tr a b = 
  convergence1 tr a b;
  ()

val lem_length : a:s
               -> b:s
               -> lst:list string
               -> Lemma (requires (forall ch. mem ch lst ==> mem_ch_s ch a /\ mem_ch_s ch b) /\
                                    (forall e. mem_ch_s e a <==> mem_ch_s e b) /\
                                   unique_chs lst /\ (forall ch. mem ch lst ==> 
                                              (forall e. C.mem_id_s e (get_msg_s ch a) <==> C.mem_id_s e (get_msg_s ch b))))
                         (ensures (forall ch. mem ch lst ==> (List.Tot.length (get_msg_s ch a) = List.Tot.length (get_msg_s ch b))))
                         (decreases lst)

let rec lem_length a b lst =
  match lst with
  |[] -> ()
  |ch::chs -> C.lem_length (get_msg_s ch a) (get_msg_s ch b);
            lem_length a b chs

val convergence3 : a:s
                 -> b:s
                 -> lst:list string
                 -> Lemma (requires (forall ch. mem ch lst ==> mem_ch_s ch a /\ mem_ch_s ch b) /\
                                      (forall e. mem_ch_s e a <==> mem_ch_s e b) /\
                                      unique_chs lst /\ (forall ch. mem ch lst ==> 
                                                 (forall e. C.mem_id_s e (get_msg_s ch a) <==> C.mem_id_s e (get_msg_s ch b))) /\
                         (forall ch. mem ch lst ==> (forall e. mem e (get_msg_s ch a) <==> mem e (get_msg_s ch b))) /\
                         (forall ch. mem ch lst ==> (List.Tot.length (get_msg_s ch a) = List.Tot.length (get_msg_s ch b))) /\
                         (forall ch. mem ch lst ==> 
                                         (forall e e1. mem e (get_msg_s ch a) /\ mem e1 (get_msg_s ch a) /\ 
                                         C.fst e <> C.fst e1 /\ C.fst e > C.fst e1 /\ C.ord e e1 (get_msg_s ch a)  <==> 
                                         mem e (get_msg_s ch b) /\ mem e1 (get_msg_s ch b) /\ C.fst e <> C.fst e1 /\
                                         C.fst e > C.fst e1 /\ C.ord e e1 (get_msg_s ch b))))
                         (ensures (forall ch. mem ch lst ==> (get_msg_s ch a = get_msg_s ch b)))
                         (decreases lst)
#set-options "--z3rlimit 10000000"
let rec convergence3 a b lst =
  match lst with
  |[] -> ()
  |ch::chs -> C.lem_same (get_msg_s ch a) (get_msg_s ch b);
            convergence3 a b chs

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall ch. mem_ch_s ch a <==> mem_ch_s ch b) /\
                                 (forall ch. mem_ch_s ch a /\ mem_ch_s ch b ==> (get_msg_s ch a = get_msg_s ch b)))

#set-options "--z3rlimit 10000000"
let convergence tr a b =
  convergence1 tr a b;
  convergence2 tr a b;
  assume (forall ch. mem ch (get_lst a) ==> mem_ch_s ch a /\ mem_ch_s ch b);
  lem_length a b (get_lst a); admit ();
  convergence3 a b (get_lst a)

val lem_oper : tr:ae op 
             -> op:(nat * op)
             -> Lemma (requires (not (member (get_id op) tr.l)))
                     (ensures (forall e. mem e (project (get_ch op) (append tr op)).l <==> 
                                    mem e (append (project (get_ch op) tr) (project_op op)).l) /\
               (forall e e1. mem e (project (get_ch op) (append tr op)).l /\
                        mem e1 (project (get_ch op) (append tr op)).l /\ (get_id e <> get_id e1) /\
                        (project (get_ch op) (append tr op)).vis e e1  <==> 
                        mem e (append (project (get_ch op) tr) (project_op op)).l /\
                    mem e1 (append (project (get_ch op) tr) (project_op op)).l /\ get_id e <> get_id e1 /\
                        (append (project (get_ch op) tr) (project_op op)).vis e e1) /\
         (forall i. i <> (get_ch op) ==> (forall e. mem e (project i (append tr op)).l <==> mem e (project i tr).l) /\
         (forall e e1. mem e (project i (append tr op)).l /\ mem e1 (project i (append tr op)).l /\ get_id e <> get_id e1 /\
                    (project i (append tr op)).vis e e1 <==> 
        mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1)))

#set-options "--z3rlimit 10000000"
let lem_oper tr op = ()

val prop_oper1 : tr:ae op
              -> st:s
              -> op:(nat * op) 
              -> Lemma (requires (sim tr st) /\ (not (member (get_id op) tr.l)) /\
                                (mem_ch_s (get_ch op) st ==> 
                                (forall id. C.mem_id_s id (get_msg_s (get_ch op) st) ==> get_id op > id)))
                      (ensures (forall ch. mem_ch_s ch (app_op st op) <==> mem_ch ch (append tr op).l) /\
                            (forall e. mem e (append tr op).l ==> (exists e1. mem e1 (app_op st op) ==> get_ch e = get_ch_s e1 /\
                                mem (get_id e, get_msg e) (get_msg_s1 e1))) /\
                                (forall ch. mem_ch_s ch (app_op st op) /\ ch <> get_ch op ==>
                      C.sim (project ch (append tr op)) (get_msg_s ch (app_op st op))))

#set-options "--z3rlimit 10000000"
let prop_oper1 tr st op = 
  lem_oper tr op

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op) 
              -> Lemma (requires (sim tr st) /\ (not (member (get_id op) tr.l)) /\
                                (mem_ch_s (get_ch op) st ==> 
                                (forall id. C.mem_id_s id (get_msg_s (get_ch op) st) ==> get_id op > id)))
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op = 
  lem_oper tr op;
  prop_oper1 tr st op;
  C.prop_oper (project (get_ch op) tr) (get_msg_s (get_ch op) st) (project_op op);
  assert (C.sim (project (get_ch op) (append tr op)) (get_msg_s (get_ch op) (app_op st op))); ()

val get_ch_lst : l:s -> a:s -> b:s
               -> Pure (list string)
                   (requires (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b))
                   (ensures (fun r -> (forall i. mem i r <==> mem_ch_s i a \/ mem_ch_s i b) /\ unique_chs r))
                   (decreases %[l;a;b])

let rec get_ch_lst l a b =
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> get_ch_lst xs a b
  |[],x::xs,_ -> if (mem_ch_s (get_ch_s x) b) then get_ch_lst [] xs b else (get_ch_s x)::(get_ch_lst [] xs b)
  |[],[],x::xs -> (get_ch_s x)::(get_ch_lst [] [] xs)

val merge1 : l:s
           -> a:s
           -> b:s
           -> lst:list string 
           -> Pure s
            (requires (forall e. mem_ch_s e l ==> mem_ch_s e a /\ mem_ch_s e b) /\ unique_chs lst /\
                      (forall ch. mem ch lst ==> (forall e. mem e (get_msg_s ch l) ==> mem e (get_msg_s ch a) /\ mem e (get_msg_s ch b)) /\
                         (forall e. mem e (C.diff_s (get_msg_s ch a) (get_msg_s ch l)) ==>
                                   not (C.mem_id_s (C.fst e) (C.diff_s (get_msg_s ch b) (get_msg_s ch l)))) /\
                         (forall e. mem e (C.diff_s (get_msg_s ch b) (get_msg_s ch l)) ==>
                                     not (C.mem_id_s (C.fst e) (C.diff_s (get_msg_s ch a) (get_msg_s ch l)))) /\
             (forall e e1. mem e (get_msg_s ch l) /\ mem e1 (C.diff_s (get_msg_s ch a) (get_msg_s ch l)) ==> C.fst e1 > C.fst e) /\
             (forall e e1. mem e (get_msg_s ch l) /\ mem e1 (C.diff_s (get_msg_s ch b) (get_msg_s ch l)) ==> C.fst e1 > C.fst e)))
               (ensures (fun r -> (forall ch. mem_ch_s ch r <==> mem ch lst) /\
                        (forall ch. mem ch lst ==> (get_msg_s ch r) =
                                   (C.merge1 (get_msg_s ch l) (get_msg_s ch a) (get_msg_s ch b)))))
             (decreases lst)

#set-options "--z3rlimit 10000000" 
let rec merge1 l a b lst =
  match lst with
  |[] -> []
  |x::xs -> (x, C.merge1 (get_msg_s x l) (get_msg_s x a) (get_msg_s x b))::merge1 l a b xs

val lem_merge1 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> a:s
            -> btr:ae op
            -> b:s
            -> lst:list string
            -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                  (forall ch. mem ch lst <==> mem_ch_s ch a \/ mem_ch_s ch b) /\ unique_chs lst)
                    (ensures (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b) /\
                      (forall ch. mem ch lst ==> (forall e. mem e (get_msg_s ch l) ==> mem e (get_msg_s ch a) /\ mem e (get_msg_s ch b))))

#set-options "--z3rlimit 10000000"
let lem_merge1 ltr l atr a btr b lst = ()

val lem_merge2 : ltr:ae op
                 -> l:s
                 -> atr:ae op
                 -> a:s
                 -> btr:ae op
                 -> b:s
                 -> lst:list string
                 -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                   (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                   (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                   (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                   (forall ch. mem ch lst <==> mem_ch_s ch a \/ mem_ch_s ch b) /\ unique_chs lst /\
                (forall ch. mem ch lst ==> (forall e. mem e (get_msg_s ch l) ==> mem e (get_msg_s ch a) /\ mem e (get_msg_s ch b))))
                    (ensures (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b) /\
                      (*forall ch. mem ch lst ==>
                             (forall e. mem e (C.diff_s (get_msg_s ch a) (get_msg_s ch l)) ==>
                                   not (C.mem_id_s (C.fst e) (C.diff_s (get_msg_s ch b) (get_msg_s ch l))))*)
                      (forall ch. mem ch lst ==>
                                 (forall e e1. mem e (C.diff_s (get_msg_s ch a) (get_msg_s ch l)) /\
                                          mem e1 (C.diff_s (get_msg_s ch b) (get_msg_s ch l)) ==> C.fst e <> C.fst e1)))

#set-options "--z3rlimit 10000000"
let lem_merge2 ltr l atr a btr b lst = ()

 val lem_merge3 : ltr:ae op
                 -> l:s
                 -> atr:ae op
                 -> a:s
                 -> btr:ae op
                 -> b:s
                 -> lst:list string
                 -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                   (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                   (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                   (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                   (forall ch. mem ch lst <==> mem_ch_s ch a \/ mem_ch_s ch b) /\ unique_chs lst)
                    (ensures (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b) /\
                      (forall ch. mem ch lst ==>
                             (forall e. mem e (C.diff_s (get_msg_s ch b) (get_msg_s ch l)) ==>
                                   not (C.mem_id_s (C.fst e) (C.diff_s (get_msg_s ch a) (get_msg_s ch l))))))

#set-options "--z3rlimit 10000000"
let lem_merge3 ltr l atr a btr b lst =
  lem_merge1 ltr l atr a btr b lst;
  lem_merge2 ltr l atr a btr b lst

val lem_merge4 : ltr:ae op
                 -> l:s
                 -> atr:ae op
                 -> a:s
                 -> btr:ae op
                 -> b:s
                 -> lst:list string
                 -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                   (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                   (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                   (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                   (forall ch. mem ch lst <==> mem_ch_s ch a \/ mem_ch_s ch b) /\ unique_chs lst)
                    (ensures (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b) /\
                      (forall ch. mem ch lst ==>
               (forall e e1. mem e (get_msg_s ch l) /\ mem e1 (C.diff_s (get_msg_s ch a) (get_msg_s ch l)) ==> C.fst e1 > C.fst e)))

#set-options "--z3rlimit 10000000"
let lem_merge4 ltr l atr a btr b lst = ()

val lem_merge5 : ltr:ae op
                 -> l:s
                 -> atr:ae op
                 -> a:s
                 -> btr:ae op
                 -> b:s
                 -> lst:list string
                 -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                   (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                   (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                   (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                   (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                   (forall ch. mem ch lst <==> mem_ch_s ch a \/ mem_ch_s ch b) /\ unique_chs lst)
                    (ensures (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b) /\
                      (forall ch. mem ch lst ==>
               (forall e e1. mem e (get_msg_s ch l) /\ mem e1 (C.diff_s (get_msg_s ch b) (get_msg_s ch l)) ==> C.fst e1 > C.fst e)))

#set-options "--z3rlimit 10000000"
let lem_merge5 ltr l atr a btr b lst = ()

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                               (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                               (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                               (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                               (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                               (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1))
                 (ensures (fun r -> (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b) /\
                                 (forall i. mem_ch_s i r <==> mem_ch_s i a \/ mem_ch_s i b) /\
                 (forall ch. mem_ch_s ch r ==> 
                 (forall e. mem e (get_msg_s ch l) ==> mem e (get_msg_s ch a) /\ mem e (get_msg_s ch b)) /\
                            (forall e. mem e (C.diff_s (get_msg_s ch a) (get_msg_s ch l)) ==>
                                      not (C.mem_id_s (C.fst e) (C.diff_s (get_msg_s ch b) (get_msg_s ch l)))) /\
                            (forall e. mem e (C.diff_s (get_msg_s ch b) (get_msg_s ch l)) ==>
                                      not (C.mem_id_s (C.fst e) (C.diff_s (get_msg_s ch a) (get_msg_s ch l)))) /\
               (forall e e1. mem e (get_msg_s ch l) /\ mem e1 (C.diff_s (get_msg_s ch a) (get_msg_s ch l)) ==> C.fst e1 > C.fst e) /\
               (forall e e1. mem e (get_msg_s ch l) /\ mem e1 (C.diff_s (get_msg_s ch b) (get_msg_s ch l)) ==> C.fst e1 > C.fst e)) /\
                               (forall ch. mem_ch_s ch r ==> (forall ch. mem_ch_s ch r ==> (get_msg_s ch r) =
                               (C.merge1 (get_msg_s ch l) (get_msg_s ch a) (get_msg_s ch b))))))

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b =
  assert (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b);
  let chs = get_ch_lst l a b in
  assert (forall i. mem i chs <==> mem_ch_s i a \/ mem_ch_s i b);
  lem_merge1 ltr l atr a btr b chs;
  lem_merge2 ltr l atr a btr b chs;
  lem_merge3 ltr l atr a btr b chs;
  lem_merge4 ltr l atr a btr b chs;
  lem_merge5 ltr l atr a btr b chs;
  let r = merge1 l a b chs in
  assert (forall ch. mem_ch_s ch r ==> (get_msg_s ch r) = (C.merge1 (get_msg_s ch l) (get_msg_s ch a) (get_msg_s ch b)));
  r

val remove_op1 : tr:ae C.op 
               -> x:(nat * C.op) 
               -> Pure (list (nat * C.op))
                      (requires (mem x tr.l))
                      (ensures (fun r -> (forall e. mem e r <==> mem e tr.l /\ e <> x) /\ unique r /\ 
                                      (List.Tot.length r = List.Tot.length tr.l - 1)))
                 (decreases tr.l)

let rec remove_op1 tr x =
  match tr.l with
  |x1::xs -> if x = x1 then xs else x1::remove_op1 (A tr.vis xs) x

val remove_op : tr:ae C.op 
              -> x:(nat * C.op) 
              -> Pure (ae C.op)
                     (requires (mem x tr.l))
                     (ensures (fun r -> (forall e. mem e r.l <==> mem e tr.l /\ e <> x) /\ unique r.l /\
                     (forall e e1. mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ e <> x /\ e1 <> x /\ tr.vis e e1 <==>
                    mem e (remove_op1 tr x) /\ mem e1 (remove_op1 tr x) /\ get_id e <> get_id e1 /\ tr.vis e e1) /\
                                (List.Tot.length r.l = List.Tot.length tr.l - 1)))
                (decreases tr.l)
let remove_op  tr x =
    (A (fun o o1 -> mem o (remove_op1 tr x) && mem o1 (remove_op1 tr x) && get_id o <> get_id o1 && tr.vis o o1) (remove_op1 tr x))

val lemma6 : l:ae op 
           -> a:ae op 
           -> Lemma (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)))
                   (ensures (forall e. mem_op e (union1 l a) <==> mem_op e l.l \/ mem_op e a.l))
                                 (decreases %[l.l;a.l])

#set-options "--z3rlimit 10000000"
let rec lemma6 l a = 
  match l,a with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma6 (A l.vis xs) a
  |(A _ []), (A _ (x::xs)) -> lemma6 l (A a.vis xs)

val lemma7 : tr:ae C.op -> s1:C.s -> tr1:ae C.op
           -> Lemma (requires C.sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                             (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                      mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                   (ensures (C.sim tr1 s1))
                     (decreases %[tr.l;s1;tr1.l])
                     [SMTPat (C.sim tr s1)]

#set-options "--z3rlimit 10000000"
let rec lemma7 tr s1 tr1 = 
  match tr.l, tr1.l with
  |[],[] -> ()
  |(id, (C.Append m))::xs, _ -> lemma7 (remove_op tr (id, (C.Append m)))
                                     (C.remove_st (id,m) s1)
                                     (remove_op tr1 (id, (C.Append m)))
  |[],(id, (C.Append m))::xs -> lemma7 tr (C.remove_st (id,m) s1) (remove_op tr1 (id, (C.Append m)))

val lemma8 : ltr:ae op 
           -> atr:ae op 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                             (forall i e. mem e (project i ltr).l ==> not (member (get_id e) (project i atr).l)) /\
                             (forall i e e1. mem e (project i ltr).l /\ mem e1 (project i atr).l ==> get_id e < get_id e1))
                   (ensures (forall i e. mem e (union (project i ltr) (project i atr)).l <==>
                                    mem e (project i (union ltr atr)).l) /\
                            (forall i. (forall e e1. (mem e (union (project i ltr) (project i atr)).l /\ 
             mem e1 (union (project i ltr) (project i atr)).l /\ get_id e <> get_id e1 /\ 
                    (union (project i ltr) (project i atr)).vis e e1) <==>
            (mem e (project i (union ltr atr)).l /\ mem e1 (project i (union ltr atr)).l /\ get_id e <> get_id e1 /\
                   (project i (union ltr atr)).vis e e1))))

#set-options "--z3rlimit 10000000"
let lemma8 ltr atr = ()

val lemma9 : ltr:ae op 
           -> atr:ae op 
           -> btr:ae op 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                             (forall i e. mem e (project i ltr).l ==> not (member (get_id e) (project i atr).l)) /\
                             (forall i e. mem e (project i atr).l ==> not (member (get_id e) (project i btr).l)) /\
                             (forall i e. mem e (project i ltr).l ==> not (member (get_id e) (project i btr).l)) /\
                           (forall i e e1. mem e (project i ltr).l /\ mem e1 (project i atr).l ==> get_id e < get_id e1) /\
                             (forall i e e1. mem e (project i ltr).l /\ mem e1 (project i btr).l ==> get_id e < get_id e1))
                   (ensures (forall i. (forall e. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l <==>
                             mem e (project i (absmerge ltr atr btr)).l)) /\
             (forall i. (forall e e1. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l /\
                  mem e1 (absmerge (project i ltr) (project i atr) (project i btr)).l /\ get_id e <> get_id e1 /\
                              (absmerge (project i ltr) (project i atr) (project i btr)).vis e e1 <==>
                                mem e (project i (absmerge ltr atr btr)).l /\ mem e1 (project i (absmerge ltr atr btr)).l /\ get_id e <> get_id e1 /\ (project i (absmerge ltr atr btr)).vis e e1)))

#set-options "--z3rlimit 10000000"
let lemma9 ltr atr btr = ()

val prop_merge1 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> chs:list string
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                  (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                  (forall i. mem_ch_s i l ==> mem_ch_s i a /\ mem_ch_s i b) /\
                                  (forall i. mem i chs ==> mem_ch_s i (merge ltr l atr a btr b)))
                        (ensures (forall i. mem i chs ==> 
                            (C.sim (project i (absmerge ltr atr btr)) (get_msg_s i (merge ltr l atr a btr b)))))
                (decreases chs)

#set-options "--z3rlimit 10000000"
let rec prop_merge1 ltr l atr a btr b lst =
  match lst with
  |[] -> ()
  |i::is -> lemma8 ltr atr; lemma8 ltr btr;
          lemma7 (project i (union ltr atr)) (get_msg_s i a) (union (project i ltr) (project i atr));
          lemma7 (project i (union ltr btr)) (get_msg_s i b) (union (project i ltr) (project i btr));
     C.prop_merge (project i ltr) (get_msg_s i l) (project i atr) (get_msg_s i a) (project i btr) (get_msg_s i b);
          lemma9 ltr atr btr;
          lemma7 (absmerge (project i ltr) (project i atr) (project i btr)) 
                 (get_msg_s i (merge ltr l atr a btr b)) (project i (absmerge ltr atr btr));
          prop_merge1 ltr l atr a btr b is


val prop_merge : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma6 ltr atr; lemma6 ltr btr;
  assert (forall ch. mem_ch_s ch (merge ltr l atr a btr b) <==> mem_ch ch (absmerge ltr atr btr).l);
  assert (forall e. mem e (absmerge ltr atr btr).l ==> (exists e1. mem e1 (merge ltr l atr a btr b) ==> 
         get_ch e = get_ch_s e1 /\ mem (get_id e, get_msg e) (get_msg_s1 e1)));
  let m = get_lst (merge ltr l atr a btr b) in
  prop_merge1 ltr l atr a btr b m

(*)instance _ : mrdt s op orset = {
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence;
  Library.sim = sim;
  Library.prop_oper = prop_oper
}*)
