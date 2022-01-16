module Sc
open FStar.List.Tot

open Library
module C = Ctr

type op = (C.op * string)

val get_item : op1:op -> Tot (s:string {(op1 = (C.Add, s))})
let get_item op1 =
  match op1 with
  |(C.Add, item) -> item

val item : s:(string * C.s) -> Tot (s1:string {(exists c. s = (s1,c))})
let item (i,_) = i

val ctr : s:(string * C.s) -> Tot (c:C.s {exists i. s = (i,c)})
let ctr (_, c) = c

val mem_item_s : item1:string 
               -> l:list (string * C.s)
               -> Tot (b:bool {b=true <==> (exists c. mem (item1,c) l)})
let rec mem_item_s item l =
  match l with
  |[] -> false
  |(item1,_)::xs -> item = item1 || mem_item_s item xs

val unique_s : list (string * C.s) -> bool
let rec unique_s l =
  match l with
  |[] -> true
  |(item,_)::xs -> not (mem_item_s item xs) && unique_s xs

type s = l:list (string * C.s) {unique_s l}

val get : item:string 
        -> s1:s {mem_item_s item s1} 
        -> Tot (i:(string * C.s) {mem i s1})
let rec get i s1 =
  match s1 with
  |(i1, c)::xs -> if i1 = i then (i1,c) else get i xs

val mem_op : item1:op
           -> l:list (nat * op)
           -> Tot (b:bool {b=true <==> (exists id. mem (id, item1) l) })
let rec mem_op item2 l =
  match l with
  |[] -> false
  |(_, item1)::xs -> item1 = item2 || mem_op item2 xs

val mem_item : i:string
             -> l:list (nat * op)
             -> Tot (b:bool {b=true <==> (exists id. mem (id, (C.Add, i)) l)})
let rec mem_item item2 l =
  match l with
  |[] -> false
  |(_, (C.Add, item1))::xs -> item1 = item2 || mem_item item2 xs

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
               -> Tot (o2:(nat * C.op) {(o2 = (get_id o1, C.Add))})
let project_op op =
  match op with
  |(id, (C.Add, i)) -> (id, C.Add)

val project1 : i:string 
             -> l:ae op
             -> Pure (list (nat * C.op))
                    (requires true)
                    (ensures (fun r -> (forall id. member id r <==> (member id l.l /\ get_op (get_eve id l.l) = (C.Add,i))) /\
                                    unique r /\ (forall e. mem e l.l /\ get_op e = (C.Add,i) ==> mem (project_op e) r) /\
                                    (C.sum r = List.Tot.length (filter (fun a -> get_op a = (C.Add,i)) l.l)) /\
                                    (forall e. mem e r ==> mem ((get_id e), (C.Add, i)) l.l)))
            (decreases List.Tot.length l.l)

#set-options "--z3rlimit 10000000"
let rec project1 i l =
  match l.l with
  |[] -> []
  |x::xs -> if get_op x = (C.Add,i) then (project_op x)::project1 i (A l.vis xs) else (project1 i (A l.vis xs))

val project : i:string
            -> l:ae op
            -> Pure (ae C.op)
                   (requires true)
                   (ensures (fun r -> (forall id. member id r.l <==> (member id l.l /\ get_op (get_eve id l.l) = (C.Add,i))) /\
                                   unique r.l /\ (forall e. mem e r.l ==> mem ((get_id e), (C.Add,i)) l.l) /\
                                   (forall e. mem e l.l /\ get_op e = (C.Add,i) ==> mem (project_op e) r.l) /\
                                   (C.sum r.l = List.Tot.length (filter (fun a -> get_op a = (C.Add,i)) l.l)) /\
                                   (forall id id1. id <> id1 /\ member id r.l /\ member id1 r.l /\ (visib id id1 r) <==> 
                                              id <> id1 /\ member id l.l /\ member id1 l.l /\ 
              get_item (get_op (get_eve id l.l)) = i /\ get_item (get_op (get_eve id1 l.l)) = i /\ (visib id id1 l))))
let project i l =
  (A (fun o o1 -> mem o (project1 i l) && mem o1 (project1 i l) && get_id o <> get_id o1 &&
    get_item (get_op (get_eve (get_id o) l.l)) = i && get_item (get_op (get_eve (get_id o1) l.l)) = i &&
               (visib (get_id o) (get_id o1) l)) (project1 i l))

val lemma1 : l:ae op
           -> Lemma (ensures (forall i. not (mem_op (C.Add,i) l.l) ==> C.sum (project i l).l = 0) /\
                            (forall i. (mem_op (C.Add,i) l.l) ==> C.sum (project i l).l <> 0) /\
                            (forall i. mem_op (C.Add,i) l.l ==> C.sum (project i l).l = 
                                  List.Tot.length (filter (fun a -> get_op a = (C.Add,i)) l.l)) /\
                            (forall e. C.sum (project e l).l = List.Tot.length (filter (fun a -> get_op a = (C.Add,e)) l.l)))
                            (decreases l.l)
                             [SMTPat (unique l.l)]

#set-options "--z3rlimit 10000000"
let rec lemma1 l = 
  match l.l with
  |[] -> ()
  |(x::xs) -> lemma1 (A l.vis xs)

val app_op : st:s -> op1:(nat * op)
           -> Pure s
             (requires (exists id i. op1 = (id, (C.Add, i))))
             (ensures (fun r -> (forall e. mem_item_s e r <==> mem_item_s e st \/ e = get_item (get_op op1)) /\
                         (not (mem_item_s (get_item (get_op op1)) st) ==> ctr (get (get_item (get_op op1)) r) = 1) /\
                            (mem_item_s (get_item (get_op op1)) st ==> 
                            ctr (get (get_item (get_op op1)) r) = ctr (get (get_item (get_op op1)) st) + 1) /\
                (forall i. i <> get_item (get_op op1) /\ mem_item_s i st ==> (ctr (get i r) = ctr (get i st))) /\
                (forall e. mem e r /\ item e = get_item (get_op op1) /\ mem_item_s (item e) st ==>
                ctr (get (get_item (get_op op1)) r) = ctr (get (get_item (get_op op1)) st) + 1) /\ unique_s r))

let rec app_op st (id, (C.Add, item)) = 
  match st with 
  |[] -> [(item, 1)]
  |(item1, c)::xs -> if item = item1 then (item1, c + 1)::xs else (item1, c)::app_op xs (id, (C.Add, item))

instance sc : datatype s op = {
  Library.app_op = app_op
}

val lemma2 : s1:s 
           -> Lemma (requires true)
                   (ensures (forall e. mem e s1 ==> (ctr (get (item e) s1) = ctr e)))
               [SMTPat (forall e. mem e s1)]
#set-options "--z3rlimit 10000000"
let rec lemma2  s1 = 
    match s1 with
    |[] -> ()
    |x::xs -> lemma2 xs 

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
          -> Tot (b:bool {(b = true) <==> (forall e. mem e s1 ==> mem_op (C.Add, (item e)) tr.l) /\
                (forall i. mem_item_s i s1 ==> (C.sim (project i tr) (ctr (get i s1)))) /\
                                   (forall e. mem e tr.l ==> mem_item_s (get_item (get_op e)) s1)})
let sim tr s1 =
  lemma1 tr; lemma2 s1;
  forallb (fun e -> mem_op (C.Add, (item e)) tr.l && ctr e = C.sum (project (item e) tr).l) s1 &&
  forallb (fun e -> mem_item_s (get_item (get_op e)) s1) tr.l

val lemma3 : tr:ae op -> s1:s
           -> Lemma (requires (sim tr s1))
                   (ensures (forall i. mem_item_s i s1 ==> (exists e. mem e tr.l /\ get_op e = (C.Add, i))) /\
                            (forall i. not (mem_item_s i s1) ==> (forall e. mem e tr.l ==> get_op e <> (C.Add, i))))
                   [SMTPat (sim tr s1)]
let lemma3 tr s1 = ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))
 
#set-options "--z3rlimit 10000000"
let prop_oper tr st op =
 if (mem_item_s (get_item (get_op op)) st) then
    C.prop_oper (project (get_item (get_op op)) tr) (ctr (get (get_item (get_op op)) st)) (project_op op)
 else ()

val convergence1 : tr:ae op
                 -> a:s
                 -> b:s
                 -> Lemma (requires (sim tr a /\ sim tr b))
                         (ensures (forall i. mem_item_s i a <==> mem_item_s i b))
let convergence1 tr a b = ()

val remove_st : i:string 
              -> s1:s
              -> Tot (r:s {(forall e. mem e r <==> mem e s1 /\ item e <> i) /\
                          (forall i1. mem_item_s i1 s1 /\ i1 <> i <==> mem_item_s i1 r) /\
                          (mem_item_s i s1 ==> List.Tot.length r = List.Tot.length s1 - 1) /\
                          (not (mem_item_s i s1) ==> List.Tot.length r = List.Tot.length s1) /\
                          not (mem_item_s i r)})
let rec remove_st i s1 =
  match s1 with
  |[] -> []
  |(i1,c)::xs -> if i=i1 then xs else (i1,c)::remove_st i xs

val lemma4 : a:s -> b:s
           -> Lemma (requires (forall i. mem_item_s i a <==> mem_item_s i b))
                   (ensures (List.Tot.length a = List.Tot.length b))
                   (decreases %[a;b])
let rec lemma4 a b =
  match a,b with
  |[],[] -> ()
  |x::xs,_ -> lemma4 xs (remove_st (item x) b)

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. mem e a <==> mem e b))
                        (decreases %[tr.l;a;b])
#set-options "--z3rlimit 100000000"
let convergence tr a b = 
  convergence1 tr a b;
  lemma4 a b;
  assert ((forall i. mem_item_s i a <==> mem_item_s i b) /\ (List.Tot.length a = List.Tot.length b));
  assert (forall i. mem_item_s i a ==> (C.sim (project i tr) (ctr (get i a))) /\
                                 (C.sim (project i tr) (ctr (get i b)))); ()

val filters : f:((string * C.s) -> bool)
             -> l:s
             -> Tot (l1:s {(forall e. mem e l1 <==> mem e l /\ f e) /\
                          (forall i. mem_item_s i l1 <==> mem_item_s i l /\ f (get i l)) /\
                          (forall i. mem_item_s i l1 ==> ctr (get i l1) = ctr (get i l))})
let rec filters f l = 
          match l with
          |[] -> []
          |hd::tl -> if f hd then hd::(filters f tl) else filters f tl

val filters_uni : f:((string * C.s) -> bool)
                   -> l:s
                   -> Lemma (requires unique_s l)
                           (ensures (unique_s (filters f l)))
                           [SMTPat (filters f l)]
let rec filters_uni f l =
      match l with
      |[] -> ()
      |x::xs -> filters_uni f xs

val unionst : a:s
            -> b:s
            -> Pure s
                (requires (forall e. mem_item_s e a ==> not (mem_item_s e b)))

                (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b) /\
                              (forall e. mem_item_s e r <==> mem_item_s e a \/ mem_item_s e b)))
let rec unionst a b =
      match a,b with
      |[],[] -> []
      |x::xs,_ -> x::unionst xs b
      |_ -> b

val un1 : l:s -> a:s -> b:s
        -> Pure s
               (requires (forall i. mem_item_s i l ==> mem_item_s i a /\ mem_item_s i b) /\
                         (forall i. mem_item_s i l ==> ctr (get i a) >= ctr (get i l) /\ ctr (get i b) >= ctr (get i l)))
         (ensures (fun r -> (forall e. mem e r <==> (mem_item_s (item e) l /\ mem_item_s (item e) a /\ mem_item_s (item e) b /\ 
                                  ctr e = ctr (get (item e) a) + ctr (get (item e) b) - ctr (get (item e) l))) /\
                         (forall i. mem_item_s i r <==> mem_item_s i l /\ mem_item_s i a /\ mem_item_s i b)))

#set-options "--z3rlimit 10000000"
let rec un1 l a b =
  match l,a,b with
  |[],[],[] -> []
  |e::xs,_,_ -> ((item e), (ctr (get (item e) a) + ctr (get (item e) b) - ctr (get (item e) l)))::un1 xs a b
  |[],_,_ -> []

val un2 : a:s -> b:s
          -> Pure s
                 (requires true)
                 (ensures (fun r -> (forall e. mem e r <==> (mem_item_s (item e) a /\ mem_item_s (item e) b /\ 
                                    ctr e = ctr (get (item e) a) + ctr (get (item e) b))) /\
                                 (forall i. mem_item_s i r <==> mem_item_s i a /\ mem_item_s i b)))
                       (decreases %[a;b])

#set-options "--initial_fuel 10 --max_fuel 10 --initial_ifuel 10 --max_ifuel 10"
#set-options "--z3rlimit 10000000"
let rec un2 a b =
  match a,b with
  |[],[] -> []
  |x::xs,_ -> if (mem_item_s (item x) b) then 
                   ((item x), (ctr (get (item x) a) + ctr (get (item x) b)))::un2 xs b
            else un2 xs b
  |[],x::xs -> []

val merge1 : l:s -> a:s -> b:s
           -> Pure (list (string * C.s))
             (requires (forall i. mem_item_s i l ==> mem_item_s i a /\ mem_item_s i b) /\
                      (forall i. mem_item_s i l ==> ctr (get i a) >= ctr (get i l) /\ ctr (get i b) >= ctr (get i l)))
                      (ensures (fun r -> (forall i. mem_item_s i r ==> 
                               (mem_item_s i a /\ mem_item_s i b /\ mem_item_s i l) \/ 
                               (mem_item_s i a /\ mem_item_s i b /\ not (mem_item_s i l)) \/
                               (mem_item_s i a /\ not (mem_item_s i b)) \/ (mem_item_s i b /\ not (mem_item_s i a))) /\
                         (forall e. mem e r <==> ((mem_item_s (item e) l /\ mem_item_s (item e) a /\ mem_item_s (item e) b /\ 
                                      (ctr e = ctr (get (item e) a) + ctr (get (item e) b) - ctr (get (item e) l))) \/
                                      (mem_item_s (item e) a /\ mem_item_s (item e) b /\ not (mem_item_s (item e) l) /\ 
                                      ctr e = ctr (get (item e) a) + ctr (get (item e) b)) \/
                           (mem_item_s (item e) a /\ not (mem_item_s (item e) b) /\ ctr e = ctr (get (item e) a)) \/
                           (mem_item_s (item e) b /\ not (mem_item_s (item e) a) /\ ctr e = ctr (get (item e) b)))) /\ unique_s r))
             (decreases %[l;a;b])

#set-options "--z3rlimit 10000000"
let merge1 l a b =
  lemma2 l; lemma2 a; lemma2 b; 
  let m1 = un1 l a b in
  assert (forall e. mem e m1 <==> (mem_item_s (item e) l /\ mem_item_s (item e) a /\ mem_item_s (item e) b /\ 
                                        (ctr e = ctr (get (item e) a) + ctr (get (item e) b) - ctr (get (item e) l)))); 
  let m2 = un2 (filters (fun a1 -> not (mem_item_s (item a1) l)) a) (filters (fun a1 -> not (mem_item_s (item a1) l)) b) in
  assert (forall e. mem_item_s e m1 ==> not (mem_item_s e m2));
  assert (forall e. mem e m2 <==> (mem_item_s (item e) a /\ mem_item_s (item e) b /\ not (mem_item_s (item e) l) /\ 
                                        ctr e = ctr (get (item e) a) + ctr (get (item e) b)));
  let m3 = filters (fun a1 -> not (mem_item_s (item a1) b)) a in
  assert (forall e. mem e m3 <==> (mem_item_s (item e) a /\ not (mem_item_s (item e) b) /\ ctr e = ctr (get (item e) a)));
  let m4 = filters (fun a1 -> not (mem_item_s (item a1) a)) b in
  assert (forall e. mem_item_s e m3 ==> not (mem_item_s e m4));
  assert (forall e. mem e m4 <==> (mem_item_s (item e) b /\ not (mem_item_s (item e) a) /\ ctr e = ctr (get (item e) b)));
  let u1 = unionst m1 m2 in
  assert (forall i. mem_item_s i u1 ==> not (mem_item_s i m3));
  let u2 = unionst u1 m3 in
  assert (forall i. mem_item_s i u2 ==> not (mem_item_s i m4));
  unionst u2 m4

val lemma5 : l:ae op 
           -> a:ae op 
           -> Lemma (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)))
                   (ensures (forall e. mem_op e (union1 l a) <==> mem_op e l.l \/ mem_op e a.l) /\
                            (forall e. C.sum (project e (union l a)).l = C.sum (project e l).l + C.sum (project e a).l))
                                (decreases %[l.l;a.l])

#set-options "--z3rlimit 10000000"
let rec lemma5 l a = 
    match l,a with
    |(A _ []), (A _ []) -> ()
    |(A _ (x::xs)), _ -> lemma5 (A l.vis xs) a
    |(A _ []), (A _ (x::xs)) -> lemma5 l (A a.vis xs)

val lem_item : l:s -> a:s -> b:s
             -> Lemma (requires (forall i. mem_item_s i l ==> mem_item_s i a /\ mem_item_s i b))
                     (ensures (forall r i. (mem_item_s i r <==>
                              (mem_item_s i a /\ mem_item_s i b /\ mem_item_s i l) \/ 
                              (mem_item_s i a /\ mem_item_s i b /\ not (mem_item_s i l)) \/
                              (mem_item_s i a /\ not (mem_item_s i b)) \/ 
                              (mem_item_s i b /\ not (mem_item_s i a))) ==>
                              (mem_item_s i r <==> mem_item_s i a \/ mem_item_s i b)))

let rec lem_item l a b = 
  match l,a,b with
  |[],[],[] -> ()
  |x::xs,_,_ -> lem_item xs a b
  |[],x::xs,_ -> lem_item [] xs b
  |[],[],_ -> ()

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
                 (ensures (fun r -> (forall i. mem_item_s i r <==> mem_item_s i a \/ mem_item_s i b) /\
                 (forall e. mem e r <==> ((mem_item_s (item e) l /\ mem_item_s (item e) a /\ mem_item_s (item e) b /\ 
                                   (ctr e = ctr (get (item e) a) + ctr (get (item e) b) - ctr (get (item e) l))) \/
                                   (mem_item_s (item e) a /\ mem_item_s (item e) b /\ not (mem_item_s (item e) l) /\ 
                                   ctr e = ctr (get (item e) a) + ctr (get (item e) b)) \/
                             (mem_item_s (item e) a /\ not (mem_item_s (item e) b) /\ ctr e = ctr (get (item e) a)) \/
                             (mem_item_s (item e) b /\ not (mem_item_s (item e) a) /\ ctr e = ctr (get (item e) b))))))

let merge ltr l atr a btr b =
  lem_item l a b;
  assert (forall i. mem_item_s i l ==> mem_item_s i a /\ mem_item_s i b);
  lemma5 ltr atr; lemma5 ltr btr;
  assert (forall i. mem_item_s i l ==> ctr (get i a) >= ctr (get i l) /\ ctr (get i b) >= ctr (get i l));
  merge1 l a b

val lemma6 : l:ae op
           -> a:ae op
           -> b:ae op
           -> Lemma (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                             (forall e. mem e l.l ==> not (member (get_id e) b.l)))
                   (ensures (forall e. mem_op e (absmerge1 l a b) <==> mem_op e l.l \/ mem_op e a.l \/ mem_op e b.l) /\
                            (forall e. (C.sum (project e (absmerge l a b)).l = 
                                  C.sum (project e l).l + C.sum (project e a).l + C.sum (project e b).l)))
                            (decreases %[l.l;a.l;b.l])

#set-options "--z3rlimit 10000000"
let rec lemma6 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma6 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma6 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma6 l a (A b.vis xs)

val lemma7 : atr:ae op 
           -> btr:ae op
           -> Lemma (requires true)
                   (ensures (forall i. (forall e. (mem e atr.l /\ get_op e = (C.Add,i)) <==> 
                                        (mem e btr.l /\ get_op e = (C.Add,i))) ==>
                                  (forall e. mem e (project i atr).l <==> mem e (project i btr).l)))
                   (decreases %[atr.l;btr.l])

#set-options "--z3rlimit 10000000"
let rec lemma7 atr btr =
  match atr, btr with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma7 (A atr.vis xs) btr
  |(A _ []), (A _ (x::xs)) -> lemma7 atr (A btr.vis xs)

val lemma8 : abs:ae op 
           -> atr:ae op 
           -> btr:ae op
           -> Lemma (requires true)
                   (ensures (forall i. (forall e. mem e abs.l /\ get_op e = (C.Add,i) <==> 
                               ((mem e btr.l /\ get_op e = (C.Add,i)) \/ (mem e atr.l /\ get_op e = (C.Add,i)))) ==>
                            (forall e. mem e (project i abs).l <==> (mem e (project i btr).l \/ mem e (project i atr).l))))
                   (decreases %[abs.l;atr.l;btr.l])

#set-options "--z3rlimit 10000000"
let rec lemma8 abs atr btr =
    match abs,atr, btr with
    |(A _ []), (A _ []), (A _ []) -> ()
    |(A _ (x::xs)), _, _ -> lemma8 (A abs.vis xs) atr btr
    |(A _ []), (A _ (x::xs)), _ -> lemma8 abs (A atr.vis xs) btr
    |(A _ []), (A _ []), (A _ (x::xs)) -> lemma8 abs atr (A btr.vis xs)

val lemma9 : abs:ae op 
           -> ltr:ae op
           -> atr:ae op
           -> btr:ae op
           -> Lemma (requires true)
                   (ensures (forall i. (forall e. mem e abs.l /\ get_op e = (C.Add,i) <==> 
                                  ((mem e btr.l /\ get_op e = (C.Add,i)) \/ (mem e ltr.l /\ get_op e = (C.Add,i)) \/ 
                                    (mem e atr.l /\ get_op e = (C.Add,i)))) ==>
                                  (forall e. mem e (project i abs).l <==> 
                                  (mem e (project i ltr).l \/ mem e (project i btr).l \/ mem e (project i atr).l))))
                      (decreases %[abs.l;ltr.l;atr.l;btr.l])

#set-options "--z3rlimit 10000000"
let rec lemma9 abs ltr atr btr =
  match abs,ltr,atr, btr with
  |(A _ []), (A _ []), (A _ []),(A _ []) -> ()
  |(A _ (x::xs)), _, _,_ -> lemma9 (A abs.vis xs) ltr atr btr
  |(A _ []), (A _ (x::xs)), _,_ -> lemma9 abs (A ltr.vis xs) atr btr
  |(A _ []), (A _ []), (A _ (x::xs)),_ -> lemma9 abs ltr (A atr.vis xs) btr
  |(A _ []), (A _ []), (A _ []), (A _ (x::xs)) -> lemma9 abs ltr atr (A btr.vis xs)

val prop_merge1 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                        (ensures (forall e. mem_item_s e a /\ not (mem_item_s e b) ==> 
                                 (C.sim (project e (absmerge ltr atr btr)) (ctr (get e (merge ltr l atr a btr b))))))

#set-options "--z3rlimit 10000000"
let prop_merge1 ltr l atr a btr b =
  lemma2 l; lemma2 a; lemma2 b; lemma2 (merge ltr l atr a btr b);
  lemma1 ltr; lemma1 (union ltr atr); lemma1 (union ltr btr); 
  lemma1 atr; lemma1 btr; lemma1 (absmerge ltr atr btr);
  lemma7 (absmerge ltr atr btr) (union ltr atr);
  lemma7 (union ltr atr) atr;
  lemma5 ltr atr; lemma5 ltr btr;
  lemma6 ltr atr btr
 (*)lemma2 l; lemma2 a; lemma2 b; lemma2 (merge ltr l atr a btr b);
 lemma1 ltr; lemma1 (union ltr atr); lemma1 (union ltr btr); 
 lemma1 atr; lemma1 btr; lemma1 (absmerge ltr atr btr); 
 assume (forall e. not (mem_item_s e b) /\ mem_item_s e a ==> (forall e1. mem e1 (union ltr btr).l ==> get_op e1 <> (C.Add, e)) /\
            (exists e1. mem e1 (union ltr atr).l /\ get_op e1 = (C.Add, e)));
 assume (forall i. not (mem_item_s i b) /\ mem_item_s i a ==> (forall e. mem e (union ltr atr).l /\ get_op e = (C.Add,i) <==>
              mem e atr.l /\ get_op e = (C.Add, i)));
 assume (forall i. not (mem_item_s i b) /\ mem_item_s i a ==> (forall e. mem e (absmerge ltr atr btr).l /\
              get_op e = (C.Add,i) <==> mem e (union ltr atr).l /\ get_op e = (C.Add, i)));
 assume (forall i. not (mem_item_s i b) /\ mem_item_s i a ==> ctr (get i (merge ltr l atr a btr b)) = ctr (get i a));
 lemma7 (absmerge ltr atr btr) (union ltr atr);
 lemma7 (union ltr atr) atr;
 assume (forall i. mem_item_s i a /\ not (mem_item_s i b) ==> (forall e. mem e (project i (absmerge ltr atr btr)).l <==> 
              mem e (project i (union ltr atr)).l));
 assume (forall i. mem_item_s i a /\ not (mem_item_s i b) ==> (forall e. mem e (project i (union ltr atr)).l <==> 
              mem e (project i atr).l)); 
 lemma5 ltr atr; lemma5 ltr btr;
 lemma6 ltr atr btr*)

val prop_merge2 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                        (ensures (forall e. mem_item_s e b /\ not (mem_item_s e a) ==> 
                                 (C.sim (project e (absmerge ltr atr btr)) (ctr (get e (merge ltr l atr a btr b))))))

#set-options "--z3rlimit 10000000"
let prop_merge2 ltr l atr a btr b =
  lemma2 l; lemma2 a; lemma2 b; lemma2 (merge ltr l atr a btr b);
  lemma1 ltr; lemma1 (union ltr atr); lemma1 (union ltr btr); 
  lemma1 atr; lemma1 btr; lemma1 (absmerge ltr atr btr);
  lemma7 (absmerge ltr atr btr) (union ltr btr);
  lemma7 (union ltr btr) btr;
  lemma5 ltr atr; lemma5 ltr btr;
  lemma6 ltr atr btr

val prop_merge3 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                        (ensures (forall e. mem_item_s e b /\ (mem_item_s e a) /\ mem_item_s e l ==> 
                                 (C.sim (project e (absmerge ltr atr btr)) (ctr (get e (merge ltr l atr a btr b))))))
                  (decreases l)

#set-options "--z3rlimit 10000000"
let prop_merge3 ltr l atr a btr b =
  lemma2 l; lemma2 a; lemma2 b; lemma2 (merge ltr l atr a btr b);
  (*)assert (forall e. (mem_item_s e l) /\ mem_item_s e a /\ mem_item_s e b ==> 
        (exists e1. mem e1 ltr.l /\ get_op e1 = (C.Add, e)) /\ (exists e1. mem e1 (union ltr btr).l /\ get_op e1 = (C.Add, e)) /\
        (exists e1. mem e1 (union ltr atr).l /\ get_op e1 = (C.Add, e)));
  assert (forall i. (mem_item_s i l) /\ mem_item_s i a /\ mem_item_s i b ==> 
            (forall e. mem e (union ltr atr).l /\ get_op e = (C.Add,i) <==> (mem e atr.l /\ get_op e = (C.Add, i)) \/ 
              (mem e ltr.l /\ get_op e = (C.Add,i))));
  assert (forall i. (mem_item_s i l) /\ mem_item_s i a /\ mem_item_s i b ==> 
              (forall e. mem e (union ltr btr).l /\ get_op e = (C.Add,i) <==> (mem e btr.l /\ get_op e = (C.Add, i)) \/
               (mem e ltr.l /\ get_op e = (C.Add,i))));
  assert (forall i. (mem_item_s i l) /\ mem_item_s i a /\ mem_item_s i b ==> 
               (forall e. mem e (absmerge ltr atr btr).l /\ get_op e = (C.Add,i) <==> 
               (mem e atr.l /\ get_op e = (C.Add, i)) \/ (mem e ltr.l /\ get_op e = (C.Add, i)) \/ 
               (mem e btr.l /\ get_op e = (C.Add,i)))); *)
  lemma9 (absmerge ltr atr btr) ltr atr btr;
  (*)assert (forall i. mem_item_s i a /\ (mem_item_s i l) /\ mem_item_s i b ==> 
         (forall e. mem e (project i (absmerge ltr atr btr)).l <==> (mem e (project i ltr).l \/
               mem e (project i atr).l \/ mem e (project i btr).l)));*)
  lemma1 ltr; lemma1 (union ltr atr); lemma1 (union ltr btr); 
  lemma1 atr; lemma1 btr; lemma1 (absmerge ltr atr btr);
  lemma5 ltr atr; lemma5 ltr btr;
  lemma6 ltr atr btr

val prop_merge4 : ltr:ae op
                -> l:s
                -> atr:ae op
                -> a:s
                -> btr:ae op
                -> b:s
                -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                  (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                        (ensures (forall e. mem_item_s e b /\ (mem_item_s e a) /\ not (mem_item_s e l) ==> 
                                 (C.sim (project e (absmerge ltr atr btr)) (ctr (get e (merge ltr l atr a btr b))))))

#set-options "--z3rlimit 10000000"
let prop_merge4 ltr l atr a btr b =
  lemma2 l; lemma2 a; lemma2 b; lemma2 (merge ltr l atr a btr b);
  (*)assert (forall e. not (mem_item_s e l) /\ mem_item_s e a /\ mem_item_s e b ==> 
           (forall e1. mem e1 ltr.l ==> get_op e1 <> (C.Add, e)) /\ (exists e1. mem e1 btr.l /\ get_op e1 = (C.Add, e)) /\
            (exists e1. mem e1 atr.l /\ get_op e1 = (C.Add, e)));
  assert (forall i. not (mem_item_s i l) /\ mem_item_s i a /\ mem_item_s i b ==> 
            (forall e. mem e (union ltr atr).l /\ get_op e = (C.Add,i) <==> mem e atr.l /\ get_op e = (C.Add, i)));
  assert (forall i. not (mem_item_s i l) /\ mem_item_s i a /\ mem_item_s i b ==> 
            (forall e. mem e (union ltr btr).l /\ get_op e = (C.Add,i) <==> mem e btr.l /\ get_op e = (C.Add, i)));

  assert (forall i. not (mem_item_s i l) /\ mem_item_s i a /\ mem_item_s i b ==> 
         (forall e. mem e (absmerge ltr atr btr).l /\ get_op e = (C.Add,i) <==> 
         (mem e atr.l /\ get_op e = (C.Add, i)) \/ (mem e btr.l /\ get_op e = (C.Add,i))));*)
  lemma7 (absmerge ltr atr btr) (union ltr atr);
  lemma7 (absmerge ltr atr btr) (union ltr btr);
  lemma7 (union ltr atr) atr;
  lemma7 (union ltr btr) btr;
  (*)assert (forall i. mem_item_s i a /\ not (mem_item_s i l) /\ mem_item_s i b ==> 
           (forall e. mem e (project i (union ltr atr)).l <==> mem e (project i atr).l));
  assert (forall i. mem_item_s i a /\ not (mem_item_s i l) /\ mem_item_s i b ==> 
              (forall e. mem e (project i (union ltr btr)).l <==> mem e (project i btr).l));*)

  lemma8 (absmerge ltr atr btr) atr btr;
  (*)assert (forall i. mem_item_s i a /\ not (mem_item_s i l) /\ mem_item_s i b ==> 
   (forall e. mem e (project i (absmerge ltr atr btr)).l <==> (mem e (project i atr).l \/ mem e (project i btr).l)));*)
  lemma1 ltr; lemma1 (union ltr atr); lemma1 (union ltr btr); 
  lemma1 atr; lemma1 btr; lemma1 (absmerge ltr atr btr);
  lemma5 ltr atr; lemma5 ltr btr;
  lemma6 ltr atr btr

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
  assert ((forall e. mem e (merge ltr l atr a btr b) ==> mem_op (C.Add, (item e)) (absmerge ltr atr btr).l) /\
          (forall e. mem e (absmerge ltr atr btr).l ==> mem_item_s (get_item (get_op e)) (merge ltr l atr a btr b)));
  prop_merge1 ltr l atr a btr b;
  prop_merge2 ltr l atr a btr b;
  prop_merge3 ltr l atr a btr b;
  prop_merge4 ltr l atr a btr b

instance _ : mrdt s op sc = {
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence;
  Library.sim = sim;
  Library.prop_oper = prop_oper
}


(*
val remove_op1 : atr:ae op 
               -> o:(nat * op)
               -> Pure (list (nat * op))
                 (requires (mem o atr.l))
                 (ensures (fun r -> (forall e. mem e r <==> mem e atr.l /\ e <> o) /\ unique r /\
            (List.Tot.length (filter (fun a -> get_op a = get_op o) r) = 
              List.Tot.length (filter (fun a -> get_op a = get_op o) atr.l) - 1)))
                          (decreases (atr.l))

#set-options "--initial_fuel 10 --max_fuel 10 --initial_ifuel 10 --max_ifuel 10"
#set-options "--z3rlimit 10000000"
let rec remove_op1  atr o =
  match atr with
  |(A _ []) -> []
  |(A _ (x::xs)) -> if x = o then xs else x::(remove_op1 (A atr.vis xs) o)

val remove_op : atr:ae op
              -> o:(nat * op)
              -> Pure (ae op)
                (requires (mem o atr.l))
                (ensures (fun r -> (forall e. mem e r.l <==> mem e atr.l /\ e <> o) /\
                                (forall e e1. mem e r.l /\ mem e1 r.l /\ get_id e <> get_id e1 /\ r.vis e e1 <==>
                                  mem e atr.l /\ mem e1 atr.l /\ get_id e <> get_id e1 /\ e <> o /\ e1 <> o /\ atr.vis e e1) /\ (List.Tot.length (filter (fun a -> get_op a = get_op o) r.l) = 
                List.Tot.length (filter (fun a -> get_op a = get_op o) atr.l) - 1)
                       ))

#set-options "--z3rlimit 10000000"
let remove_op atr o =
  (A (fun e e1 -> (mem e atr.l && mem e1 atr.l && get_id e <> get_id e1 && e <> o && e1 <> o && atr.vis e e1))
               (remove_op1 atr o))
               
               
               (*)val prove : ltr:ae op
                    -> l:s
                    -> atr:ae op
                    -> a:s
                    -> btr:ae op
                    -> b:s
                    
                    -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                      (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                      (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                      (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) (*)/\
                                      (forall e. mem e abs.l <==> mem e (absmerge ltr atr btr).l) /\
                                      (forall e e1. mem e abs.l /\ mem e1 abs.l /\ get_id e <> get_id e1 /\ abs.vis e e1 <==>
                                         mem e (absmerge ltr atr btr).l /\ mem e1 (absmerge ltr atr btr).l /\
                                         get_id e <> get_id e1 /\ (absmerge ltr atr btr).vis e e1*))
                            (ensures (forall e. mem_item_s e a /\ not (mem_item_s e b) ==> 
                    (C.sim (project e (absmerge ltr atr btr)) (ctr (get e (merge ltr l atr a btr b))))))
                    (decreases %[ltr.l;l;atr.l;a;btr.l;b])

#set-options "--z3rlimit 10000000"
let rec prove ltr l atr a btr b =
 match l,a,b with
 |[],[],[] -> ()
 |(i,c)::xs,_,_ -> admit(); prove (sub_ae (fun a1 -> get_op a1 <> (C.Add,i)) ltr) xs 
                       (sub_ae (fun a1 -> get_op a1 <> (C.Add,i)) atr) (remove_st i a)
                       (sub_ae (fun a1 -> get_op a1 <> (C.Add,i)) btr) (remove_st i b)
 |[],(i,c)::xs,_ -> if not (mem_item_s i b) then
                    (lemma3sc ltr atr; lemma3sc ltr btr; lemma1sc1 ltr atr btr;
                    C.prop_merge (project i ltr) 0 (project i atr) c (project i btr) 0;
                    assume (C.sim (project i (absmerge ltr atr btr)) c);
                    prove ltr l (sub_ae (fun a1 -> get_op a1 <> (C.Add,i)) atr) xs btr b;
                    admit ())
                 else (admit(); prove ltr l (sub_ae (fun a1 -> get_op a1 <> (C.Add,i)) atr) xs
                                  (sub_ae (fun a1 -> get_op a1 <> (C.Add,i)) btr) (remove_st i b))
 |[],[],_ -> admit ()*)*)
