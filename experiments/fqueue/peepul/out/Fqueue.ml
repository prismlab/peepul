open Prims

type op =
  | Enqueue of Prims.nat 
  | Dequeue of (Prims.nat * Prims.nat) FStar_Pervasives_Native.option 
let (uu___is_Enqueue : op -> Prims.bool) =
  fun projectee -> match projectee with | Enqueue _0 -> true | uu___ -> false
let (__proj__Enqueue__item___0 : op -> Prims.nat) =
  fun projectee -> match projectee with | Enqueue _0 -> _0
let (uu___is_Dequeue : op -> Prims.bool) =
  fun projectee -> match projectee with | Dequeue _0 -> true | uu___ -> false
let (__proj__Dequeue__item___0 :
  op -> (Prims.nat * Prims.nat) FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Dequeue _0 -> _0
type o = (Prims.nat * op)
let get_id : 'uuuuu 'uuuuu1 . ('uuuuu * 'uuuuu1) -> 'uuuuu =
  fun uu___ -> match uu___ with | (id1, uu___1) -> id1
let get_op : 'uuuuu 'uuuuu1 . ('uuuuu * 'uuuuu1) -> 'uuuuu1 =
  fun uu___ -> match uu___ with | (uu___1, op1) -> op1
let (is_enqueue : o -> Prims.bool) =
  fun v ->
    match v with
    | (uu___, Enqueue uu___1) -> true
    | (uu___, Dequeue uu___1) -> false
let (is_dequeue : o -> Prims.bool) =
  fun v ->
    match v with
    | (uu___, Enqueue uu___1) -> false
    | (uu___, Dequeue uu___1) -> true
let (get_ele : o -> Prims.nat) =
  fun uu___ -> match uu___ with | (id1, Enqueue x) -> x
let (return : o -> (Prims.nat * Prims.nat) FStar_Pervasives_Native.option) =
  fun uu___ -> match uu___ with | (id1, Dequeue x) -> x
let rec (mem_id :
  Prims.nat -> (Prims.nat * Prims.nat) Prims.list -> Prims.bool) =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id1, uu___)::xs -> (id1 = n) || (mem_id n xs)
let rec (unique_id : (Prims.nat * Prims.nat) Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | (id1, uu___)::xs ->
        (Prims.op_Negation (mem_id id1 xs)) && (unique_id xs)
let rec (position :
  (Prims.nat * Prims.nat) -> (Prims.nat * Prims.nat) Prims.list -> Prims.nat)
  =
  fun e ->
    fun s1 ->
      match s1 with
      | x::xs ->
          if e = x then Prims.int_zero else Prims.int_one + (position e xs)
let (order :
  (Prims.nat * Prims.nat) ->
    (Prims.nat * Prims.nat) ->
      (Prims.nat * Prims.nat) Prims.list -> Prims.bool)
  = fun e1 -> fun e2 -> fun s1 -> (position e1 s1) < (position e2 s1)
let rec (rev_acc :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  =
  fun l ->
    fun acc -> match l with | [] -> acc | hd::tl -> rev_acc tl (hd :: acc)
let (rev :
  (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list) =
  fun l -> rev_acc l []


















type s =
  | S of (Prims.nat * Prims.nat) Prims.list * (Prims.nat * Prims.nat)
  Prims.list 
let (uu___is_S : s -> Prims.bool) = fun projectee -> true
let (__proj__S__item__front : s -> (Prims.nat * Prims.nat) Prims.list) =
  fun projectee -> match projectee with | S (front, back) -> front
let (__proj__S__item__back : s -> (Prims.nat * Prims.nat) Prims.list) =
  fun projectee -> match projectee with | S (front, back) -> back
let (memq : (Prims.nat * Prims.nat) -> s -> Prims.bool) =
  fun n ->
    fun q ->
      (FStar_List_Tot_Base.mem n (__proj__S__item__front q)) ||
        (FStar_List_Tot_Base.mem n (__proj__S__item__back q))
let rec (app :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], []) -> []
      | (x::xs, []) -> x :: xs
      | (x::xs, uu___) -> x :: (app xs l2)
      | ([], x::xs) -> x :: xs
let (tolist : s -> (Prims.nat * Prims.nat) Prims.list) =
  fun uu___ -> match uu___ with | S (f, b) -> app f (rev b)
let (norm : s -> s) =
  fun q -> match q with | S ([], back) -> S ((rev back), []) | uu___ -> q
let (peek : s -> (Prims.nat * Prims.nat) FStar_Pervasives_Native.option) =
  fun q ->
    let n = norm q in
    match n with
    | S ([], []) -> FStar_Pervasives_Native.None
    | S (x::uu___, uu___1) -> FStar_Pervasives_Native.Some x
let rec (last_ele :
  (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat)) =
  fun l -> match l with | x::[] -> x | x::xs -> last_ele xs
let (rear : s -> (Prims.nat * Prims.nat) FStar_Pervasives_Native.option) =
  fun q ->
    match q with
    | S ([], []) -> FStar_Pervasives_Native.None
    | S (uu___, x::uu___1) -> FStar_Pervasives_Native.Some x
    | S (x, []) -> FStar_Pervasives_Native.Some (last_ele x)









let (enqueue : (Prims.nat * Prims.nat) -> s -> s) =
  fun x ->
    fun s1 ->
      S ((__proj__S__item__front s1), (x :: (__proj__S__item__back s1)))
let (get_val :
  (Prims.nat * Prims.nat) FStar_Pervasives_Native.option ->
    (Prims.nat * Prims.nat))
  = fun a -> match a with | FStar_Pervasives_Native.Some (x, y) -> (x, y)
let (is_empty : s -> Prims.bool) =
  fun s1 ->
    ((__proj__S__item__front s1) = []) && ((__proj__S__item__back s1) = [])
let (dequeue :
  s -> ((Prims.nat * Prims.nat) FStar_Pervasives_Native.option * s)) =
  fun q ->
    match q with
    | S ([], []) -> (FStar_Pervasives_Native.None, q)
    | S (x::xs, uu___) ->
        ((FStar_Pervasives_Native.Some x),
          (S (xs, (__proj__S__item__back q))))
    | S ([], x::xs) ->
        let uu___ = norm q in
        (match uu___ with
         | S (y::ys, []) -> ((FStar_Pervasives_Native.Some y), (S (ys, []))))
let (app_op : s -> o -> s) =
  fun s1 ->
    fun e ->
      match e with
      | (id1, Enqueue n) -> enqueue (id1, n) s1
      | (uu___, Dequeue x) -> FStar_Pervasives_Native.snd (dequeue s1)
let rec (member : Prims.nat -> o Prims.list -> Prims.bool) =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id1, uu___)::xs -> (n = id1) || (member n xs)
let rec (unique : o Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | (id1, uu___)::xs -> (Prims.op_Negation (member id1 xs)) && (unique xs)
type ae =
  | A of (o -> o -> Prims.bool) * o Prims.list 
let (uu___is_A : ae -> Prims.bool) = fun projectee -> true
let (__proj__A__item__vis : ae -> o -> o -> Prims.bool) =
  fun projectee -> match projectee with | A (vis, l) -> vis
let (__proj__A__item__l : ae -> o Prims.list) =
  fun projectee -> match projectee with | A (vis, l) -> l
let (matched : o -> o -> ae -> Prims.bool) =
  fun e ->
    fun d ->
      fun tr ->
        (((((is_enqueue e) && (is_dequeue d)) &&
             (FStar_List_Tot_Base.mem e (__proj__A__item__l tr)))
            && (FStar_List_Tot_Base.mem d (__proj__A__item__l tr)))
           &&
           ((return d) =
              (FStar_Pervasives_Native.Some ((get_id e), (get_ele e)))))
          && (__proj__A__item__vis tr e d)
let rec (sub_list : o -> o Prims.list -> o Prims.list) =
  fun e ->
    fun l -> match l with | x::xs -> if x = e then xs else sub_list e xs
let rec (position_o : o -> o Prims.list -> Prims.nat) =
  fun e ->
    fun s1 ->
      match s1 with
      | x::xs ->
          if e = x then Prims.int_zero else Prims.int_one + (position_o e xs)
let (ord : o -> o -> o Prims.list -> Prims.bool) =
  fun e1 -> fun e2 -> fun s1 -> (position_o e1 s1) < (position_o e2 s1)
let rec (ob : o -> o -> o Prims.list -> Prims.bool) =
  fun e ->
    fun d ->
      fun l ->
        match l with
        | x::xs ->
            if x = e
            then FStar_List_Tot_Base.mem d xs
            else if x <> d then ob e d xs else false
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x > y then x else y
let rec (len_del : o Prims.list -> Prims.int) =
  fun l ->
    match l with
    | [] -> Prims.int_zero
    | x::xs ->
        if is_enqueue x
        then Prims.int_one + (len_del xs)
        else (Prims.of_int (-1)) + (len_del xs)
let (is_empty' : o Prims.list -> s -> Prims.bool) =
  fun l ->
    fun s1 ->
      (((FStar_List_Tot_Base.length (__proj__S__item__front s1)) +
          (FStar_List_Tot_Base.length (__proj__S__item__back s1)))
         + (len_del l))
        = Prims.int_zero
let rec (filter_s :
  ((Prims.nat * Prims.nat) -> Prims.bool) ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl -> if f hd then hd :: (filter_s f tl) else filter_s f tl
let rec (filter_op : (o -> Prims.bool) -> o Prims.list -> o Prims.list) =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl -> if f hd then hd :: (filter_op f tl) else filter_op f tl

let rec (sorted : (Prims.nat * Prims.nat) Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | uu___::[] -> true
    | x::y::xs ->
        ((FStar_Pervasives_Native.fst x) < (FStar_Pervasives_Native.fst y))
          && (sorted (y :: xs))

let (test_sorted2 : unit -> (Prims.nat * Prims.nat) Prims.list) =
  fun uu___ -> []

type ('l1, 'l2) permutation = unit
type ('l, 'l1, 'l2) permutation_2 = unit
type ('l, 'l1, 'l2) split_inv = unit

let rec forall_mem :
  'uuuuu . 'uuuuu Prims.list -> ('uuuuu -> Prims.bool) -> Prims.bool =
  fun l ->
    fun f ->
      match l with
      | [] -> true
      | hd::tl -> if f hd then forall_mem tl f else false
let rec exists_mem :
  'uuuuu . 'uuuuu Prims.list -> ('uuuuu -> Prims.bool) -> Prims.bool =
  fun l ->
    fun f ->
      match l with
      | [] -> false
      | hd::tl -> if f hd then true else exists_mem tl f
let (sim0 : ae -> s -> Prims.bool) =
  fun tr ->
    fun s0 ->
      let enq_list =
        filter_op
          (fun x ->
             ((is_enqueue x) &&
                (FStar_List_Tot_Base.mem x (__proj__A__item__l tr)))
               &&
               (Prims.op_Negation
                  (exists_mem (__proj__A__item__l tr)
                     (fun d ->
                        ((is_dequeue d) && ((get_id x) <> (get_id d))) &&
                          (matched x d tr))))) (__proj__A__item__l tr) in
      if
        (forall_mem enq_list
           (fun x ->
              ((FStar_List_Tot_Base.mem x (__proj__A__item__l tr)) &&
                 (is_enqueue x))
                &&
                (FStar_List_Tot_Base.mem ((get_id x), (get_ele x))
                   (tolist s0))))
          &&
          (forall_mem (tolist s0)
             (fun x ->
                FStar_List_Tot_Base.mem
                  ((FStar_Pervasives_Native.fst x),
                    (Enqueue (FStar_Pervasives_Native.snd x))) enq_list))
      then true
      else false
let (sim1 : ae -> s -> Prims.bool) =
  fun tr ->
    fun s0 ->
      let enq_list =
        filter_op
          (fun x ->
             ((is_enqueue x) &&
                (FStar_List_Tot_Base.mem x (__proj__A__item__l tr)))
               &&
               (Prims.op_Negation
                  (exists_mem (__proj__A__item__l tr)
                     (fun d ->
                        (((is_dequeue d) &&
                            (FStar_List_Tot_Base.mem d
                               (__proj__A__item__l tr)))
                           && ((get_id x) <> (get_id d)))
                          && (matched x d tr))))) (__proj__A__item__l tr) in
      forall_mem (tolist s0)
        (fun e ->
           forall_mem
             (filter_s
                (fun e1 ->
                   (((memq e s0) && (memq e1 s0)) &&
                      ((FStar_Pervasives_Native.fst e) <>
                         (FStar_Pervasives_Native.fst e1)))
                     && (order e e1 (tolist s0))) (tolist s0))
             (fun e1 ->
                (((FStar_List_Tot_Base.mem
                     ((FStar_Pervasives_Native.fst e),
                       (Enqueue (FStar_Pervasives_Native.snd e))) enq_list)
                    &&
                    (FStar_List_Tot_Base.mem
                       ((FStar_Pervasives_Native.fst e1),
                         (Enqueue (FStar_Pervasives_Native.snd e1))) enq_list))
                   &&
                   ((FStar_Pervasives_Native.fst e) <>
                      (FStar_Pervasives_Native.fst e1)))
                  &&
                  ((__proj__A__item__vis tr
                      ((FStar_Pervasives_Native.fst e),
                        (Enqueue (FStar_Pervasives_Native.snd e)))
                      ((FStar_Pervasives_Native.fst e1),
                        (Enqueue (FStar_Pervasives_Native.snd e1))))
                     ||
                     ((Prims.op_Negation
                         ((__proj__A__item__vis tr
                             ((FStar_Pervasives_Native.fst e),
                               (Enqueue (FStar_Pervasives_Native.snd e)))
                             ((FStar_Pervasives_Native.fst e1),
                               (Enqueue (FStar_Pervasives_Native.snd e1))))
                            ||
                            (__proj__A__item__vis tr
                               ((FStar_Pervasives_Native.fst e1),
                                 (Enqueue (FStar_Pervasives_Native.snd e1)))
                               ((FStar_Pervasives_Native.fst e),
                                 (Enqueue (FStar_Pervasives_Native.snd e))))))
                        &&
                        ((get_id
                            ((FStar_Pervasives_Native.fst e),
                              (Enqueue (FStar_Pervasives_Native.snd e))))
                           <
                           (get_id
                              ((FStar_Pervasives_Native.fst e1),
                                (Enqueue (FStar_Pervasives_Native.snd e1)))))))))
let (sim2 : ae -> s -> Prims.bool) =
  fun tr ->
    fun s0 ->
      let enq_list =
        filter_op
          (fun x ->
             ((is_enqueue x) &&
                (FStar_List_Tot_Base.mem x (__proj__A__item__l tr)))
               &&
               (Prims.op_Negation
                  (exists_mem (__proj__A__item__l tr)
                     (fun d ->
                        (((is_dequeue d) &&
                            (FStar_List_Tot_Base.mem d
                               (__proj__A__item__l tr)))
                           && ((get_id x) <> (get_id d)))
                          && (matched x d tr))))) (__proj__A__item__l tr) in
      forall_mem enq_list
        (fun e ->
           (is_enqueue e) &&
             (forall_mem
                (filter_op
                   (fun e1 ->
                      ((is_enqueue e1) && ((get_id e) <> (get_id e1))) &&
                        ((__proj__A__item__vis tr e e1) ||
                           ((Prims.op_Negation
                               ((__proj__A__item__vis tr e e1) ||
                                  (__proj__A__item__vis tr e1 e)))
                              && ((get_id e) < (get_id e1))))) enq_list)
                (fun e1 ->
                   ((((is_enqueue e1) && (memq ((get_id e), (get_ele e)) s0))
                       && (memq ((get_id e1), (get_ele e1)) s0))
                      && ((get_id e) <> (get_id e1)))
                     &&
                     (order ((get_id e), (get_ele e))
                        ((get_id e1), (get_ele e1)) (tolist s0)))))
let (sim : ae -> s -> Prims.bool) =
  fun tr -> fun s0 -> ((sim0 tr s0) && (sim1 tr s0)) && (sim2 tr s0)
let (append : ae -> o -> ae) =
  fun tr ->
    fun op1 ->
      match tr with
      | A (uu___, ops) ->
          A
            (((fun o1 ->
                 fun o11 ->
                   ((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l tr)) &&
                        (FStar_List_Tot_Base.mem o11 (__proj__A__item__l tr)))
                       && ((get_id o1) <> (get_id o11)))
                      && (__proj__A__item__vis tr o1 o11))
                     ||
                     (((FStar_List_Tot_Base.mem o1 (__proj__A__item__l tr))
                         && (o11 = op1))
                        && ((get_id o1) <> (get_id op1))))), (op1 :: ops))
let rec (union_list_ae : ae -> ae -> o Prims.list) =
  fun l ->
    fun a ->
      match (l, a) with
      | (A (uu___, []), A (uu___1, [])) -> []
      | (A (uu___, x::xs), uu___1) -> x ::
          (union_list_ae (A ((__proj__A__item__vis l), xs)) a)
      | (A (uu___, []), A (uu___1, x::xs)) -> x ::
          (union_list_ae l (A ((__proj__A__item__vis a), xs)))
let (union : ae -> ae -> ae) =
  fun l ->
    fun a ->
      A
        ((fun o1 ->
            fun o11 ->
              (((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)) &&
                    (FStar_List_Tot_Base.mem o11 (__proj__A__item__l l)))
                   && ((get_id o1) <> (get_id o11)))
                  && (__proj__A__item__vis l o1 o11))
                 ||
                 ((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l a)) &&
                      (FStar_List_Tot_Base.mem o11 (__proj__A__item__l a)))
                     && ((get_id o1) <> (get_id o11)))
                    && (__proj__A__item__vis a o1 o11)))
                ||
                (((FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)) &&
                    (FStar_List_Tot_Base.mem o11 (__proj__A__item__l a)))
                   && ((get_id o1) <> (get_id o11)))), (union_list_ae l a))
let rec (absmerge_list_ae : ae -> ae -> ae -> o Prims.list) =
  fun l ->
    fun a ->
      fun b ->
        match (l, a, b) with
        | (A (uu___, []), A (uu___1, []), A (uu___2, [])) -> []
        | (A (uu___, x::xs), uu___1, uu___2) -> x ::
            (absmerge_list_ae (A ((__proj__A__item__vis l), xs)) a b)
        | (A (uu___, []), A (uu___1, x::xs), uu___2) -> x ::
            (absmerge_list_ae l (A ((__proj__A__item__vis a), xs)) b)
        | (A (uu___, []), A (uu___1, []), A (uu___2, x::xs)) -> x ::
            (absmerge_list_ae l a (A ((__proj__A__item__vis b), xs)))
let (absmerge : ae -> ae -> ae -> ae) =
  fun l ->
    fun a ->
      fun b ->
        A
          ((fun o1 ->
              fun o11 ->
                (((((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)) &&
                        (FStar_List_Tot_Base.mem o11 (__proj__A__item__l l)))
                       && ((get_id o1) <> (get_id o11)))
                      && (__proj__A__item__vis l o1 o11))
                     ||
                     ((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l a))
                          &&
                          (FStar_List_Tot_Base.mem o11 (__proj__A__item__l a)))
                         && ((get_id o1) <> (get_id o11)))
                        && (__proj__A__item__vis a o1 o11)))
                    ||
                    ((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l b)) &&
                         (FStar_List_Tot_Base.mem o11 (__proj__A__item__l b)))
                        && ((get_id o1) <> (get_id o11)))
                       && (__proj__A__item__vis b o1 o11)))
                   ||
                   ((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)) &&
                        (FStar_List_Tot_Base.mem o11 (__proj__A__item__l a)))
                       && ((get_id o1) <> (get_id o11)))
                      && (__proj__A__item__vis (union l a) o1 o11)))
                  ||
                  ((((FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)) &&
                       (FStar_List_Tot_Base.mem o11 (__proj__A__item__l b)))
                      && ((get_id o1) <> (get_id o11)))
                     && (__proj__A__item__vis (union l b) o1 o11))),
            (absmerge_list_ae l a b))
let rec (diff_s :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  =
  fun a ->
    fun l ->
      match (a, l) with
      | (x::xs, y::ys) ->
          if
            (FStar_Pervasives_Native.fst y) < (FStar_Pervasives_Native.fst x)
          then diff_s (x :: xs) ys
          else diff_s xs ys
      | ([], y::ys) -> []
      | (uu___, []) -> a
let rec (intersection :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list ->
      (Prims.nat * Prims.nat) Prims.list ->
        (Prims.nat * Prims.nat) Prims.list)
  =
  fun l ->
    fun a ->
      fun b ->
        match (l, a, b) with
        | (x::xs, y::ys, z::zs) ->
            if
              ((FStar_Pervasives_Native.fst x) <
                 (FStar_Pervasives_Native.fst y))
                ||
                ((FStar_Pervasives_Native.fst x) <
                   (FStar_Pervasives_Native.fst z))
            then intersection xs (y :: ys) (z :: zs)
            else x :: (intersection xs ys zs)
        | (x::xs, [], z::zs) -> []
        | (x::xs, y::ys, []) -> []
        | (x::xs, [], []) -> []
        | ([], uu___, uu___1) -> []
let rec (union_s :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  =
  fun a ->
    fun b ->
      match (a, b) with
      | ([], []) -> []
      | (x::xs, []) -> x :: xs
      | ([], x::xs) -> x :: xs
      | (x::xs, y::ys) -> x :: (union_s xs b)
let rec (split :
  (Prims.nat * Prims.nat) Prims.list ->
    ((Prims.nat * Prims.nat) Prims.list * (Prims.nat * Prims.nat) Prims.list))
  =
  fun uu___ ->
    match uu___ with
    | x::y::l ->
        (match l with
         | [] -> ([x], [y])
         | x'::[] -> ([x; x'], [y])
         | uu___1 ->
             let uu___2 = split l in
             (match uu___2 with | (l1, l2) -> ((x :: l1), (y :: l2))))
type ('l1, 'l2, 'l) merge_inv = unit
let rec (merge_sl :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], uu___) -> l2
      | (uu___, []) -> l1
      | (h1::tl1, h2::tl2) ->
          if
            (FStar_Pervasives_Native.fst h1) <
              (FStar_Pervasives_Native.fst h2)
          then h1 :: (merge_sl tl1 l2)
          else h2 :: (merge_sl l1 tl2)
let rec (mergesort :
  (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list) =
  fun l ->
    match l with
    | [] -> []
    | x::[] -> [x]
    | uu___ ->
        let uu___1 = split l in
        (match uu___1 with
         | (l1, l2) ->
             let sl1 = mergesort l1 in
             let sl2 = mergesort l2 in merge_sl sl1 sl2)

let (sort :
  (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list) =
  fun l -> mergesort l
let rec (union1 :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], []) -> []
      | ([], l21) -> l21
      | (l11, []) -> l11
      | (h1::t1, h2::t2) ->
          if
            (FStar_Pervasives_Native.fst h1) <
              (FStar_Pervasives_Native.fst h2)
          then h1 :: (union1 t1 l2)
          else h2 :: (union1 l1 t2)
let (sorted_union :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list -> (Prims.nat * Prims.nat) Prims.list)
  = fun a -> fun b -> union1 a b
let (merge_s :
  (Prims.nat * Prims.nat) Prims.list ->
    (Prims.nat * Prims.nat) Prims.list ->
      (Prims.nat * Prims.nat) Prims.list ->
        (Prims.nat * Prims.nat) Prims.list)
  =
  fun l ->
    fun a ->
      fun b ->
        let ixn = intersection l a b in
        let diff_a = diff_s a l in
        let diff_b = diff_s b l in
        let union_ab = sorted_union diff_a diff_b in
        let res = union_s ixn union_ab in res
let (merge : ae -> s -> ae -> s -> ae -> s -> s) =
  fun ltr ->
    fun l ->
      fun atr ->
        fun a ->
          fun btr ->
            fun b ->
              let res = S ((merge_s (tolist l) (tolist a) (tolist b)), []) in
              res
