(* open Prims *)
type op =
  | Add 
  | Rem 
let (uu___is_Add : op -> bool) =
  fun projectee -> match projectee with | Add -> true | uu___ -> false
let (uu___is_Rem : op -> bool) =
  fun projectee -> match projectee with | Rem -> true | uu___ -> false
type o = (int * op * int)
let get_id : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu
  = fun uu___ -> match uu___ with | (id, uu___1, uu___2) -> id
let get_op : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu1
  = fun uu___ -> match uu___ with | (uu___1, op1, uu___2) -> op1
let get_ele :
  'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu2 =
  fun uu___ -> match uu___ with | (uu___1, uu___2, ele) -> ele
let rec (member_s :
  int -> (int * int) list -> bool) =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id, uu___)::xs -> (n = id) || (member_s n xs)
let rec (unique_s : (int * int) list -> bool) =
  fun l ->
    match l with
    | [] -> true
    | (id, uu___)::xs ->
        (Prims.op_Negation (member_s id xs)) && (unique_s xs)
type s = (int * int) list
type t = (int * int) list [@@deriving irmin]

let rec forallb : 'a . ('a -> bool) -> 'a list -> bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | hd::tl -> if f hd then forallb f tl else false
let rec existsb : 'a . ('a -> bool) -> 'a list -> bool =
  fun f ->
    fun l ->
      match l with
      | [] -> false
      | hd::tl -> if f hd then true else existsb f tl
let rec filter : 'a . ('a -> bool) -> 'a list -> 'a list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl -> if f hd then hd :: (filter f tl) else filter f tl
let rec except : 'a . ('a -> bool) -> 'a list -> 'a list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl ->
          if Prims.op_Negation (f hd)
          then hd :: (except f tl)
          else except f tl

let rec (app_op : s -> o -> s) =
  fun s1 ->
    fun uu___ ->
      match uu___ with
      | (id, op1, ele) ->
          (match op1 with
           | Add -> (id, ele) :: s1
           | Rem ->
               filter (fun e -> (FStar_Pervasives_Native.snd e) <> ele) s1)
let rec (member : int -> o list -> bool) =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id, uu___, uu___1)::xs -> (n = id) || (member n xs)
let rec (unique : o list -> bool) =
  fun l ->
    match l with
    | [] -> true
    | (id, uu___, uu___1)::xs ->
        (Prims.op_Negation (member id xs)) && (unique xs)
type ae =
  | A of (o -> o -> bool) * o list 
let (uu___is_A : ae -> bool) = fun projectee -> true
let (__proj__A__item__vis : ae -> o -> o -> bool) =
  fun projectee -> match projectee with | A (vis, l) -> vis
let (__proj__A__item__l : ae -> o list) =
  fun projectee -> match projectee with | A (vis, l) -> l
let (sim : ae -> s -> bool) =
  fun tr ->
    fun s1 ->
      let lsta = filter (fun a -> (get_op a) = Add) (__proj__A__item__l tr) in
      let lstr = filter (fun r -> (get_op r) = Rem) (__proj__A__item__l tr) in
      let lst =
        except
          (fun a ->
             existsb
               (fun r ->
                  (((get_id a) <> (get_id r)) && ((get_ele r) = (get_ele a)))
                    && (__proj__A__item__vis tr a r)) lstr) lsta in
      (forallb
         (fun e -> FStar_List_Tot_Base.mem ((get_id e), (get_ele e)) s1) lst)
        &&
        (forallb
           (fun e ->
              FStar_List_Tot_Base.mem
                ((FStar_Pervasives_Native.fst e), Add,
                  (FStar_Pervasives_Native.snd e)) lst) s1)
let rec (union1 : ae -> ae -> o list) =
  fun l ->
    fun a ->
      match (l, a) with
      | (A (uu___, []), A (uu___1, [])) -> []
      | (A (uu___, x::xs), uu___1) -> x ::
          (union1 (A ((__proj__A__item__vis l), xs)) a)
      | (A (uu___, []), A (uu___1, x::xs)) -> x ::
          (union1 l (A ((__proj__A__item__vis a), xs)))
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
                   && ((get_id o1) <> (get_id o11)))), (union1 l a))
let rec (absmerge1 : ae -> ae -> ae -> o list) =
  fun l ->
    fun a ->
      fun b ->
        match (l, a, b) with
        | (A (uu___, []), A (uu___1, []), A (uu___2, [])) -> []
        | (A (uu___, x::xs), uu___1, uu___2) -> x ::
            (absmerge1 (A ((__proj__A__item__vis l), xs)) a b)
        | (A (uu___, []), A (uu___1, x::xs), uu___2) -> x ::
            (absmerge1 l (A ((__proj__A__item__vis a), xs)) b)
        | (A (uu___, []), A (uu___1, []), A (uu___2, x::xs)) -> x ::
            (absmerge1 l a (A ((__proj__A__item__vis b), xs)))
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
            (absmerge1 l a b))
let rec (diff2 :
  (int * int) list ->
    (int * int) list -> (int * int) list)
  =
  fun a ->
    fun l ->
      filter (fun e -> Prims.op_Negation (FStar_List_Tot_Base.mem e l)) a
let rec (remove : s -> (int * int) -> s) =
  fun l -> fun ele -> filter (fun e -> e <> ele) l
let rec (merge_s : s -> s -> s -> s) =
  fun l ->
    fun a ->
      fun b ->
        match (l, a, b) with
        | ([], [], []) -> []
        | (x::xs, uu___, uu___1) ->
            if (FStar_List_Tot_Base.mem x a) && (FStar_List_Tot_Base.mem x b)
            then x :: (merge_s xs (remove a x) (remove b x))
            else
              if FStar_List_Tot_Base.mem x a
              then merge_s xs (remove a x) b
              else
                if FStar_List_Tot_Base.mem x b
                then merge_s xs a (remove b x)
                else merge_s xs a b
        | ([], x::xs, uu___) -> x :: (merge_s [] xs b)
        | ([], [], x::xs) -> b
let (merge1 : ae -> s -> ae -> s -> ae -> s -> s) =
  fun ltr -> fun l -> fun atr -> fun a -> fun btr -> fun b -> merge_s l a b

let merge ~old a b =
	let open Irmin.Merge.Infix in
	old () >>=* fun old ->
  let _old = (match old with None -> [] | Some l -> l) in
  Irmin.Merge.ok (merge_s _old a b)

let merge = Irmin.Merge.(option (v t merge))

let (append : ae -> o -> ae) =
  fun tr ->
    fun op1 ->
      match tr with
      | A (uu___, []) ->
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
                        && ((get_id o1) <> (get_id op1))))), [op1])
      | A (uu___, x::xs) ->
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
                        && ((get_id o1) <> (get_id op1))))), (op1 :: x ::
              xs))

