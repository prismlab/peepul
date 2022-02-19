module Log
open FStar.List.Tot

open Library

val fst : e:(nat * string) -> Tot (id:nat {exists m. e = (id, m)})
let fst (id, m) = id

val snd : e:(nat * string) -> Tot (m:string {exists id. e = (id, m)})
let snd (id, m) = m

val mem_id_s : id:nat 
             -> l:list (nat * string) 
             -> Tot (b:bool {b = true <==> (exists m. mem (id,m) l) /\ (exists e. mem e l ==> fst e = id)})
let rec mem_id_s id l =
  match l with
  |[] -> false
  |(id1,m)::xs -> id = id1 || mem_id_s id xs

val unique_s : l:list (nat * string) -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |(id,m)::xs -> not (mem_id_s id xs) && unique_s xs

val pos : id:(nat * string) 
        -> l:list (nat * string) {mem id l /\ unique_s l} 
        -> Tot nat
let rec pos id l =
  match l with
  |id1::xs -> if id = id1 then 0 else 1 + pos id xs

val total_order : l:list (nat * string) {unique_s l} -> Tot bool
let rec total_order l =
  match l with
  |[] -> true
  |[x] -> true
  |x::xs ->  forallb (fun e -> fst x > fst e) xs && total_order xs

val test_sorted: x:(nat * string) -> l:list (nat * string) ->
                        Lemma ((unique_s (x::l) /\ total_order (x::l) /\ Cons? l) ==> fst x > fst (Cons?.hd l))
let test_sorted x l = ()

val ord : id:(nat * string)
        -> id1:(nat * string) {fst id <> fst id1}
        -> l:list (nat * string) {mem id l /\ mem id1 l /\ unique_s l /\ total_order l}
        -> Tot (b:bool {b = true <==> pos id l < pos id1 l})
let ord id id1 l = pos id l < pos id1 l 

val sorted_smaller: x:(nat * string)
                  ->  y:(nat * string)
                  ->  l:list (nat * string)
                  ->  Lemma (requires (unique_s (x::l) /\ total_order (x::l) /\ mem y l))
                           (ensures (fst x > fst y) /\ ord x y (x::l))
                                    [SMTPat (unique_s (x::l) /\ total_order (x::l))]

#set-options "--z3rlimit 1000000"
let rec sorted_smaller x y l = match l with
          | [] -> ()
          | z::zs -> if z=y then () else sorted_smaller x y zs

type s = l: list (nat (*id*) * string (*message*)) {unique_s l /\ total_order l}

val filter_uni : f:((nat * string) -> bool)
               -> l:list (nat * string) 
               -> Lemma (requires (unique_s l /\ total_order l))
                       (ensures (unique_s (filter f l) /\ total_order (filter f l)) /\
                                 (forall e. mem e l /\ f e <==> mem e (filter f l)) /\
                          (forall e e1. mem e l /\ mem e1 l /\ f e /\ f e1 /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l <==>
       mem e (filter f l) /\ mem e1 (filter f l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (filter f l)))
                               [SMTPat (filter f l)]

#set-options "--z3rlimit 1000000"
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

type op =
  |Append : string (*message*) -> op

val get_msg : op1:(nat * op) -> Tot (s:string {exists id. op1 = (id, (Append s))}) 
let get_msg (id, (Append m)) = m

val get_id : op1:(nat * op) -> Tot (id:nat {exists m. op1 = (id, (Append m))}) 
let get_id (id, (Append m)) = id

val app_op : s1:s 
           -> op1:(nat * op)
           -> Pure s 
             (requires not (mem_id_s (get_id op1) s1) /\ (forall id. mem_id_s id s1 ==> get_id op1 > id))
             (ensures (fun r -> (forall e. mem e r <==> mem e s1 \/ e = (get_id op1, get_msg op1)) /\
                             (forall e e1. mem e s1 /\ mem e1 s1 /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 s1 <==>
                                      mem e r /\ mem e1 r /\ fst e <> fst e1 /\ fst e > fst e1 /\
                             e <> (get_id op1, get_msg op1) /\ e1 <> (get_id op1, get_msg op1) /\ ord e e1 r)))
#set-options "--z3rlimit 1000000"
let app_op s1 (id, (Append m)) = (id, m)::s1

val filter_uni1 : f:((nat * op) -> bool)
                -> l:list (nat * op) 
                -> Lemma (requires (unique l))
                        (ensures (unique (filter f l)))
                           [SMTPat (filter f l)]
let rec filter_uni1 f l = 
  match l with
  |[] -> ()
  |x::xs -> filter_uni1 f xs

(*)instance log : datatype s op = {
  Library.app_op = app_op
}*)

val filter_s : f:((nat * string) -> bool)
             -> l:s
             -> Tot (l1:s {forall e. mem e l1 <==> mem e l /\ f e})
let rec filter_s  f l = 
          match l with
          |[] -> []
          |hd::tl -> if f hd then hd::(filter_s f tl) else filter_s f tl

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> (forall e. mem e s1 <==> mem (fst e, (Append (snd e))) tr.l) /\
                                     (forall e e1. (mem (fst e, (Append (snd e))) tr.l /\ 
                                          mem (fst e1, (Append (snd e1))) tr.l /\ fst e <> fst e1 /\ fst e > fst e1) <==>
                                          mem e s1 /\ mem e1 s1 /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 s1)})

#set-options "--z3rlimit 1000000"
let sim tr s1 = 
  forallb (fun e -> mem (fst e, (Append (snd e))) tr.l) s1 &&
  forallb (fun e -> mem (get_id e, get_msg e) s1) tr.l &&
  forallb (fun e -> (forallb (fun e1 -> (mem (fst e, (Append (snd e))) tr.l && mem (fst e1, (Append (snd e1))) tr.l &&
              fst e <> fst e1 && fst e > fst e1))
  (filter_s (fun e1 -> mem e1 s1 && mem e s1 && fst e <> fst e1 && fst e > fst e1 && ord e e1 s1) s1))) s1 &&
  forallb (fun e -> (forallb (fun e1 -> mem (get_id e, get_msg e) s1 && mem (get_id e1, get_msg e1) s1 && get_id e <> get_id e1 && get_id e > get_id e1 && ord (get_id e, get_msg e) (get_id e1, get_msg e1) s1)
          (filter (fun e1 -> (get_id e <> get_id e1 && get_id e > get_id e1)) tr.l))) tr.l

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (forall id. mem_id_s id st ==> get_id op > id) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 1000000"
let prop_oper tr st op = ()

val remove_st : ele:(nat * string) -> a:s
                  -> Pure s
                    (requires (mem ele a))
                    (ensures (fun r -> (forall e. mem e r <==> mem e a /\ e <> ele) /\
                                    (forall e e1. mem e r /\ mem e1 r /\ fst e <> fst e1 /\ ord e e1 r /\ fst e > fst e1 <==>
                         mem e a /\ mem e1 a /\ fst e <> fst e1 /\ e <> ele /\ e1 <> ele /\ fst e > fst e1 /\ ord e e1 a)))

#set-options "--z3rlimit 1000000"
let remove_st ele a = filter (fun e -> e <> ele) a

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall id. mem_id_s id a <==> mem_id_s id b) /\ (forall e. mem e a <==> mem e b) /\
                                 (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ ord e e1 a /\ fst e > fst e1 <==> 
                                          mem e b /\ mem e1 b /\ fst e <> fst e1 /\ ord e e1 b /\ fst e > fst e1))
let convergence tr a b = ()

val union_s : a:s
            -> b:s
            -> Pure s
                 (requires (forall e. mem e a ==> not (mem_id_s (fst e) b)) /\ 
                           (forall e. mem e b ==> not (mem_id_s (fst e) a)))
                   (ensures (fun u -> (forall e. mem e u <==> mem e a \/ mem e b)/\
                                 (forall e e1. ((mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a) \/
                                 (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b) \/
                                 (mem e a /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1) \/
                                 (mem e b /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1)) <==>
                                 (mem e u /\ mem e1 u /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 u))))

#set-options "--z3rlimit 10000000"
let rec union_s l1 l2 =
    match l1, l2 with
    | [], [] -> []
    | [], l2 -> l2
    | l1, [] -> l1
    | h1::t1, h2::t2 -> if (fst h1 > fst h2)
                     then h1::(union_s t1 l2) else h2::(union_s l1 t2)

val diff_s : a:s -> l:s
           -> Pure s
             (requires (forall e. mem e l ==> mem e a))
             (ensures (fun r -> (forall e. mem e r <==> mem e a /\ not (mem e l)) /\
                             (forall e e1. mem e r /\ mem e1 r /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 r <==>
             mem e a /\ mem e1 a /\ not (mem e l) /\ not (mem e1 l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a)))
let diff_s a l = filter (fun e -> not (mem e l)) a

val merge1 : l:s
           -> a:s
           -> b:s
           -> Pure s
             (requires (forall e. mem e l ==> mem e a /\ mem e b) /\
                       (forall e. mem e (diff_s a l) ==> not (mem_id_s (fst e) (diff_s b l))) /\
                       (forall e. mem e (diff_s b l) ==> not (mem_id_s (fst e) (diff_s a l))) /\
                       (forall e e1. mem e l /\ mem e1 (diff_s a l) ==> fst e1 > fst e) /\
                       (forall e e1. mem e l /\ mem e1 (diff_s b l) ==> fst e1 > fst e) (*)/\
                       (forall e e1. mem e l /\ mem e1 a ==> fst e1 >= fst e) /\
                       (forall e e1. mem e l /\ mem e1 b ==> fst e1 >= fst e*) /\
                       (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a <==>
                                (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l) \/
              (mem e (diff_s a l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s a l)) \/
              (mem e (diff_s a l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1)) /\
              (forall e e1. mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b <==>
                                 (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l) \/
                 (mem e (diff_s b l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s b l)) \/
                 (mem e (diff_s b l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1)) /\
      (forall e e1. mem e l /\ mem e1 l /\ mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l ==> ord e e1 a) /\
      (forall e e1. mem e l /\ mem e1 l /\ mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l ==> ord e e1 b))
             (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b) /\
                            (forall e e1. mem e r /\ mem e1 r /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 r <==>
                                      (mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a) \/
                                     (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b) \/
                                     (mem e a /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1) \/
                                     (mem e b /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1)) (*)/\
                            (forall e e1. mem e r /\ mem e1 r /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 r <==>
                                     (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l) \/
            (mem e (diff_s a l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s a l)) \/
            (mem e (diff_s b l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s b l)) \/
            (mem e (diff_s a l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1) \/
            (mem e (diff_s b l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1) \/
            (mem e (diff_s a l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1) \/
            (mem e (diff_s b l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1)*)))

#set-options "--z3rlimit 10000000"
let merge1 l a b =
    let la = diff_s a l in
    assert (forall e e1. mem e l /\ mem e1 la ==> fst e1 > fst e); 
    let lb = diff_s b l in
    assert (unique_s lb /\ total_order lb);
    assert ((forall e. mem e la ==> not (mem_id_s (fst e) lb)) /\ 
            (forall e. mem e lb ==> not (mem_id_s (fst e) la))); 
    let u = union_s la lb in
    assert ((forall e. mem e l ==> not (mem_id_s (fst e) u)) /\ 
            (forall e. mem e u ==> not (mem_id_s (fst e) l))); 
    let r = union_s u l in 
    assert (forall e e1. mem e r /\ mem e1 r /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 r <==>
                                      (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l) \/
             (mem e (diff_s a l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s a l)) \/
             (mem e (diff_s b l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s b l)) \/
             (mem e (diff_s a l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1) \/
             (mem e (diff_s b l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1) \/
             (mem e (diff_s a l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1) \/
             (mem e (diff_s b l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1));
      assert (forall e. mem e l \/ mem e (diff_s a l) \/ mem e (diff_s b l) <==> mem e a \/ mem e b); 
      assert (forall e e1. ((mem e l /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l) \/
             (mem e (diff_s a l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s a l)) \/
             (mem e (diff_s b l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s b l)) \/
                     (mem e (diff_s a l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1) \/
                     (mem e (diff_s b l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1) \/
                     (mem e (diff_s a l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1) \/
                     (mem e (diff_s b l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1)) ==>
                  ((mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a) \/
                                       (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b) \/
                                       (mem e a /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1) \/
                                       (mem e b /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1))); admit();
    r

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b) /\
                               (forall e e1. mem e r /\ mem e1 r /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 r <==>
                                        (mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a) \/
                                        (mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b) \/
                                        (mem e a /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1) \/
                                        (mem e b /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1))))

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b = 
    assert (forall e. mem e l ==> mem e a /\ mem e b);
    assert ((forall e. mem e (diff_s a l) ==> not (mem_id_s (fst e) (diff_s b l))) /\
            (forall e. mem e (diff_s b l) ==> not (mem_id_s (fst e) (diff_s a l))));
    assert ((forall e e1. mem e l /\ mem e1 (diff_s a l) ==> fst e1 > fst e) /\
            (forall e e1. mem e l /\ mem e1 (diff_s b l) ==> fst e1 > fst e)); 
    assert (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a <==>
                (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l) \/
             (mem e (diff_s a l) /\ mem e1 (diff_s a l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s a l)) \/
                (mem e (diff_s a l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1)); 
    assert (forall e e1. mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b <==>
                                   (mem e l /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l) \/
              (mem e (diff_s b l) /\ mem e1 (diff_s b l) /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 (diff_s b l)) \/
                  (mem e (diff_s b l) /\ mem e1 l /\ fst e <> fst e1 /\ fst e > fst e1)); 
    assert ((forall e e1. mem e l /\ mem e1 l /\ mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l ==> ord e e1 a) /\
    (forall e e1. mem e l /\ mem e1 l /\ mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 l ==> ord e e1 b));
    merge1 l a b

val prop_merge : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
    assert (forall e. mem e (merge ltr l atr a btr b) <==> mem (fst e, (Append (snd e))) (absmerge ltr atr btr).l);
    assert (forall e e1. mem e (merge ltr l atr a btr b) /\ mem e1 (merge ltr l atr a btr b) /\ fst e <> fst e1 /\ 
                fst e > fst e1 /\ ord e e1 (merge ltr l atr a btr b) ==>
                mem (fst e, (Append (snd e))) (absmerge ltr atr btr).l /\ 
                mem (fst e1, (Append (snd e1))) (absmerge ltr atr btr).l /\
                fst e <> fst e1 /\ fst e > fst e1);
    assert (forall e e1. mem e (absmerge ltr atr btr).l /\ mem e1 (absmerge ltr atr btr).l /\ get_id e <> get_id e1 /\ 
                    get_id e > get_id e1 ==> mem (get_id e, get_msg e) (merge ltr l atr a btr b) /\ 
                        mem (get_id e1, get_msg e1) (merge ltr l atr a btr b) /\
             get_id e <> get_id e1 /\ get_id e > get_id e1 /\ 
             ord (get_id e, get_msg e) (get_id e1, get_msg e1) (merge ltr l atr a btr b));
    ()

(*)instance _ : mrdt s op log = {
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence;
  Library.sim = sim;
  Library.prop_oper = prop_oper*)

