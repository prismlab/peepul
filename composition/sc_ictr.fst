module Sc_ictr
open FStar.List.Tot

open Library
module C = Ictr

type op = (C.op * string)

val get_item : op1:op -> Tot (s:string {(op1 = (C.Add, s))})
let get_item op1 =
  match op1 with
  |(C.Add, item) -> item

val item : s:(string * C.s) -> Tot (s1:string {(exists c. s = (s1,c))})
let item (i,_) = i

val mem_item_s : item1:string 
               -> l:list (string * C.s)
               -> Tot (b:bool {b=true <==> (exists c. mem (item1,c) l) /\ (exists e. mem e l /\ item e = item1)})
let rec mem_item_s item1 l =
  match l with
  |[] -> false
  |x::xs -> item x = item1 || mem_item_s item1 xs

val unique_s : list (string * C.s) -> bool
let rec unique_s l =
  match l with
  |[] -> true
  |(item,_)::xs -> not (mem_item_s item xs) && unique_s xs

type s = l:list (string * C.s) {unique_s l}

val ctr1 : s:(string * C.s) -> Tot (c:C.s {(exists i. s = (i,c)) /\ s = (item s, c)})
let ctr1 (_, c) = c

val ctr : i:string -> s1:s -> Tot (c:C.s {(mem_item_s i s1 ==> mem (i,c) s1 /\ (exists e. mem e s1 ==> e = (i,c))) /\ 
                                       (not (mem_item_s i s1) ==> c = 0)})
let rec ctr i s1 =
  match s1 with
  |[] -> 0
  |x::xs -> if item x = i then (ctr1 x) else ctr i xs

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
                         (not (mem_item_s (get_item (get_op op1)) st) ==> ctr (get_item (get_op op1)) r = 1) /\
                            (mem_item_s (get_item (get_op op1)) st ==> 
                            ctr (get_item (get_op op1)) r = ctr (get_item (get_op op1)) st + 1) /\
                (forall i. i <> get_item (get_op op1) /\ mem_item_s i st ==> (ctr i r = ctr i st)) /\
                (forall e. mem e r /\ item e = get_item (get_op op1) /\ mem_item_s (item e) st ==>
                ctr (get_item (get_op op1)) r = ctr (get_item (get_op op1)) st + 1) /\ unique_s r))

let rec app_op st (id, (C.Add, item)) = 
  match st with 
  |[] -> [(item, 1)]
  |(item1, c)::xs -> if item = item1 then (item1, c + 1)::xs else (item1, c)::app_op xs (id, (C.Add, item))

instance sc : datatype s op = {
  Library.app_op = app_op
}

val lemma2 : s1:s 
           -> Lemma (requires true)
                   (ensures (forall e. mem e s1 ==> (ctr (item e) s1 = ctr1 e)))
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
                                     (forall i. mem_item_s i s1 ==>  (C.sim (project i tr) (ctr i s1))) /\
                                     (forall e. mem e tr.l ==> mem_item_s (get_item (get_op e)) s1)})
let sim tr s1 = 
  lemma1 tr; lemma2 s1;
  forallb (fun e -> mem_op (C.Add, (item e)) tr.l && ctr1 e = C.sum (project (item e) tr).l) s1 &&
  forallb (fun e -> mem_item_s (get_item (get_op e)) s1) tr.l

val lemma3 : tr:ae op -> s1:s
           -> Lemma (requires (sim tr s1))
                   (ensures (forall i. mem_item_s i s1 ==> (exists e. mem e tr.l /\ get_op e = (C.Add, i))) /\
                            (forall i. not (mem_item_s i s1) ==> (forall e. mem e tr.l ==> get_op e <> (C.Add, i))))
                   [SMTPat (sim tr s1)]
let lemma3 tr s1 = ()

val lemma4 : tr:ae op -> s1:s
           -> Lemma (requires sim tr s1)
                   (ensures (forall i. (C.sim (project i tr) (ctr i s1))))
                   [SMTPat (sim tr s1)]
let lemma4 tr s1 = ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 10000000"
let prop_oper tr st op =
  C.prop_oper (project (get_item (get_op op)) tr) (ctr (get_item (get_op op)) st) (project_op op)

val get_lst : m:s -> Pure (list string)
                    (requires true)
                    (ensures (fun r -> (forall i. mem i r <==> mem_item_s i m)))
let rec get_lst m =
   match m with
   |[] -> []
   |(i,x)::xs -> i::get_lst xs

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

val lemma5 : a:s -> b:s
           -> Lemma (requires (forall i. mem_item_s i a <==> mem_item_s i b))
                   (ensures (List.Tot.length a = List.Tot.length b))
                   (decreases %[a;b])
let rec lemma5 a b =
  match a,b with
  |[],[] -> ()
  |x::xs,_ -> lemma5 xs (remove_st (item x) b)

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. mem e a <==> mem e b))
                        (decreases %[tr.l;a;b])

#set-options "--z3rlimit 100000000"
let convergence tr a b = 
  convergence1 tr a b;
  lemma5 a b;
  assert ((forall i. mem_item_s i a <==> mem_item_s i b) /\ (List.Tot.length a = List.Tot.length b));
  assert (forall i. mem_item_s i a ==> (C.sim (project i tr) (ctr i a)) /\
                                 (C.sim (project i tr) (ctr i b))); ()

val lemma6 : l:ae op 
           -> a:ae op 
           -> Lemma (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)))
                   (ensures (forall e. mem_op e (union1 l a) <==> mem_op e l.l \/ mem_op e a.l) /\
                            (forall e. C.sum (project e (union l a)).l = C.sum (project e l).l + C.sum (project e a).l))
                                (decreases %[l.l;a.l])

#set-options "--z3rlimit 10000000"
let rec lemma6 l a = 
    match l,a with
    |(A _ []), (A _ []) -> ()
    |(A _ (x::xs)), _ -> lemma6 (A l.vis xs) a
    |(A _ []), (A _ (x::xs)) -> lemma6 l (A a.vis xs)

val unique_items : list string -> Tot bool
let rec unique_items l =
  match l with
  |[] -> true
  |x::xs -> not (mem x xs) && unique_items xs

val get_item_lst : l:s -> a:s -> b:s
                 -> Pure (list string)
                   (requires (forall i. mem_item_s i l ==> mem_item_s i a /\ mem_item_s i b))
                   (ensures (fun r -> (forall i. mem i r <==> mem_item_s i a \/ mem_item_s i b) /\ unique_items r))
                   (decreases %[l;a;b])

let rec get_item_lst l a b =
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> assert (mem_item_s (item x) a /\ mem_item_s (item x) b); get_item_lst xs a b
  |[],x::xs,_ -> if (mem_item_s (item x) b) then get_item_lst [] xs b else (item x)::(get_item_lst [] xs b)
  |[],[],x::xs -> (item x)::(get_item_lst [] [] xs)

val merge1 : l:s 
           -> a:s 
           -> b:s {(forall i. mem_item_s i l ==> mem_item_s i a /\ mem_item_s i b) /\
                  (forall i. mem_item_s i l ==> ctr i a >= ctr i l /\ ctr i b >= ctr i l)} 
           -> lst:list string {unique_items lst} 
           -> Tot (r:s {(forall i. mem_item_s i r <==> mem i lst) /\
                       (forall e. mem_item_s e r ==> (ctr e r = C.merge1 (ctr e l) (ctr e a)  (ctr e b)))})
                 (decreases %[lst])

#set-options "--z3rlimit 10000000"
let rec merge1 l a b lst = 
  match lst with
  |[] -> []
  |i::is -> (i, C.merge1 (ctr i l) (ctr i a) (ctr i b))::merge1 l a b is

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
                               (forall i. mem_item_s i l ==> ctr i a >= ctr i l /\ ctr i b >= ctr i l) /\
                               (forall i. mem_item_s i r ==> (ctr i r = C.merge1 (ctr i l) (ctr i a) (ctr i b)))))
                        (decreases %[l;a;b])

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b = 
  lemma6 ltr atr; lemma6 ltr btr;
  let lst = get_item_lst l a b in
  merge1 l a b lst

val lemma7 : tr:ae C.op -> s1:C.s -> tr1:ae C.op
           -> Lemma (requires C.sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l))
                   (ensures (C.sim tr1 s1))
                   (decreases %[tr.l;s1;tr1.l])
                   [SMTPat (C.sim tr s1)]

let rec lemma7 tr s1 tr1 = 
  match tr.l, tr1.l with
  |[],[] -> ()
  |x::xs,_ -> lemma7 (remove_op tr x) (s1 - 1) (remove_op tr1 x)

val lemma8 : ltr:ae op -> atr:ae op 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e i. mem e (project i ltr).l ==> not (member (get_id e) (project i atr).l)))
                   (ensures ((forall e i. mem e (union (project i ltr) (project i atr)).l <==> mem e (project i (union ltr atr)).l)))
                               (decreases %[ltr.l;atr.l])

#set-options "--z3rlimit 10000000"
let lemma8 ltr atr = ()
  
val lemma9 : ltr:ae op -> atr:ae op -> btr:ae op
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (forall i e. mem e (project i ltr).l ==> not (member (get_id e) (project i atr).l)) /\
                             (forall i e. mem e (project i atr).l ==> not (member (get_id e) (project i btr).l)) /\
                             (forall i e. mem e (project i ltr).l ==> not (member (get_id e) (project i btr).l)))
                   (ensures (forall i. (forall e. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l <==>
                              mem e (project i (absmerge ltr atr btr)).l)))
                               (decreases %[ltr.l;atr.l;btr.l])

#set-options "--z3rlimit 10000000"
let lemma9 ltr atr btr = ()

val prop_merge1 : ltr:ae op
                 -> l:s
                 -> atr:ae op
                 -> a:s
                 -> btr:ae op
                 -> b:s
                 -> items:list string
                 -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                   (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                   (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                   (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                                   (forall i. mem_item_s i l ==> ctr i a >= ctr i l /\ ctr i b >= ctr i l) /\
                                   (forall i. mem_item_s i l ==> mem_item_s i a /\ mem_item_s i b) /\
                                   (forall i. mem i items ==> mem_item_s i (merge ltr l atr a btr b)))
                         (ensures (forall i. mem i items ==> 
                                   (C.sim (project i (absmerge ltr atr btr)) (ctr i (merge ltr l atr a btr b)))))
                (decreases items)

#set-options "--z3rlimit 10000000"
let rec prop_merge1 ltr l atr a btr b lst =
  match lst with
  |[] -> ()
  |i::is -> lemma8 ltr atr; lemma8 ltr btr;
          lemma7 (project i (union ltr atr)) (ctr i a) (union (project i ltr) (project i atr));
          lemma7 (project i (union ltr btr)) (ctr i b) (union (project i ltr) (project i btr));
          C.prop_merge (project i ltr) (ctr i l) (project i atr) (ctr i a) (project i btr) (ctr i b);
          lemma9 ltr atr btr;
          lemma7 (absmerge (project i ltr) (project i atr) (project i btr)) 
                 (ctr i (merge ltr l atr a btr b)) (project i (absmerge ltr atr btr));
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
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma6 ltr atr; lemma6 ltr btr;
  let m = get_lst (merge ltr l atr a btr b) in
  prop_merge1 ltr l atr a btr b m

instance _ : mrdt s op sc = {
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence;
  Library.sim = sim;
  Library.prop_oper = prop_oper
}


(*#set-options "--z3rlimit 10000000"
let rec prop_merge1 ltr l atr a btr b lst =
  (*)lemma5 ltr atr; lemma5 ltr btr;*)
  match lst with
  |[] -> ()
  |i::is -> assert (forall e. mem e (project i ltr).l ==> not (member (get_id e) (project i atr).l)); 
          assert (forall e. mem e (project i ltr).l ==> not (member (get_id e) (project i btr).l));
          lem_un i ltr atr; lem_un i ltr btr;
          assert (forall e. mem e (union (project i ltr) (project i atr)).l <==> mem e (project i (union ltr atr)).l);
          assert (forall e. mem e (union (project i ltr) (project i btr)).l <==> mem e (project i (union ltr btr)).l);
          same (project i (union ltr atr)) (ctr i a) (union (project i ltr) (project i atr));
          same (project i (union ltr btr)) (ctr i b) (union (project i ltr) (project i btr));
          assert (C.sim (project i ltr) (ctr i l)); 
          assert ((C.sim (project i ltr) (ctr i l))); 
          assert ((C.sim (project i ltr) (ctr i l) /\ 
                   C.sim (union (project i ltr) (project i atr)) (ctr i a) /\ 
                   C.sim (union (project i ltr) (project i btr)) (ctr i b))); 
          C.prop_merge (project i ltr) (ctr i l) (project i atr) (ctr i a) (project i btr) (ctr i b);
      assert (C.sim (absmerge (project i ltr) (project i atr) (project i btr)) (ctr i (merge ltr l atr a btr b)));
      assert ((forall  e. mem e (project i ltr).l ==> not (member (get_id e) (project i atr).l)) /\
                  (forall  e. mem e (project i atr).l ==> not (member (get_id e) (project i btr).l)) /\
                  (forall  e. mem e (project i ltr).l ==> not (member (get_id e) (project i btr).l)));
      lem_abs i ltr atr btr;
      assert (forall e. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l <==> mem e (project i (absmerge ltr atr btr)).l); 
      same (absmerge (project i ltr) (project i atr) (project i btr)) (ctr i (merge ltr l atr a btr b)) (project i (absmerge ltr atr btr));
          assert (C.sim (project i (absmerge ltr atr btr)) (ctr i (merge ltr l atr a btr b)));
          prop_merge1 ltr l atr a btr b is*)


  (*)if (mem_item_s (get_item (get_op op)) st) then
      C.prop_oper (project (get_item (get_op op)) tr) (ctr (get_item (get_op op)) st) (project_op op)
  else ()*)
