open Prims
type ('state, 'operation) datatype =
  {
  app_op: 'state -> (Prims.nat * 'operation) -> 'state }
let __proj__Mkdatatype__item__app_op :
  'state 'operation .
    ('state, 'operation) datatype ->
      'state -> (Prims.nat * 'operation) -> 'state
  = fun projectee -> match projectee with | { app_op;_} -> app_op
let app_op :
  'state .
    unit ->
      ('state, Obj.t) datatype -> 'state -> (Prims.nat * Obj.t) -> 'state
  = fun operation -> fun d -> __proj__Mkdatatype__item__app_op d
let get_id : 'op . (Prims.nat * 'op) -> Prims.nat =
  fun uu___ -> match uu___ with | (id, uu___1) -> id
let get_op : 'op . (Prims.nat * 'op) -> 'op =
  fun uu___ -> match uu___ with | (uu___1, op1) -> op1
let rec member :
  'op . Prims.nat -> (Prims.nat * 'op) Prims.list -> Prims.bool =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id, uu___)::xs -> (n = id) || (member n xs)
let rec unique : 'op . (Prims.nat * 'op) Prims.list -> Prims.bool =
  fun l ->
    match l with
    | [] -> true
    | (id, uu___)::xs -> (Prims.op_Negation (member id xs)) && (unique xs)
let rec get_eve :
  'op . Prims.nat -> (Prims.nat * 'op) Prims.list -> (Prims.nat * 'op) =
  fun id ->
    fun l ->
      match l with
      | (id1, x)::xs -> if id = id1 then (id1, x) else get_eve id xs
type 'op ae =
  | A of ((Prims.nat * 'op) -> (Prims.nat * 'op) -> Prims.bool) * (Prims.nat
  * 'op) Prims.list 
let uu___is_A : 'op . 'op ae -> Prims.bool = fun projectee -> true
let __proj__A__item__vis :
  'op . 'op ae -> (Prims.nat * 'op) -> (Prims.nat * 'op) -> Prims.bool =
  fun projectee -> match projectee with | A (vis, l) -> vis
let __proj__A__item__l : 'op . 'op ae -> (Prims.nat * 'op) Prims.list =
  fun projectee -> match projectee with | A (vis, l) -> l
let rec get_op_id : 'op . Prims.nat -> 'op ae -> 'op =
  fun id ->
    fun l ->
      match __proj__A__item__l l with
      | (id1, op1)::xs ->
          if id = id1
          then op1
          else get_op_id id (A ((__proj__A__item__vis l), xs))
let append : 'op . 'op ae -> (Prims.nat * 'op) -> 'op ae =
  fun tr ->
    fun op1 ->
      match tr with
      | A (uu___, []) ->
          A
            (((fun o ->
                 fun o1 ->
                   ((((FStar_List_Tot_Base.mem o (__proj__A__item__l tr)) &&
                        (FStar_List_Tot_Base.mem o1 (__proj__A__item__l tr)))
                       && ((get_id o) <> (get_id o1)))
                      && (__proj__A__item__vis tr o o1))
                     ||
                     (((FStar_List_Tot_Base.mem o (__proj__A__item__l tr)) &&
                         (o1 = op1))
                        && ((get_id o) <> (get_id op1))))), [op1])
      | A (uu___, x::xs) ->
          A
            (((fun o ->
                 fun o1 ->
                   ((((FStar_List_Tot_Base.mem o (__proj__A__item__l tr)) &&
                        (FStar_List_Tot_Base.mem o1 (__proj__A__item__l tr)))
                       && ((get_id o) <> (get_id o1)))
                      && (__proj__A__item__vis tr o o1))
                     ||
                     (((FStar_List_Tot_Base.mem o (__proj__A__item__l tr)) &&
                         (o1 = op1))
                        && ((get_id o) <> (get_id op1))))), (op1 :: x :: xs))
let rec forallb : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | hd::tl -> if f hd then forallb f tl else false
let rec existsb : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> false
      | hd::tl -> if f hd then true else existsb f tl
let rec filter : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl -> if f hd then hd :: (filter f tl) else filter f tl
let visib : 'op . Prims.nat -> Prims.nat -> 'op ae -> Prims.bool =
  fun id ->
    fun id1 ->
      fun l ->
        if
          existsb
            (fun e ->
               ((get_id e) = id) &&
                 (existsb
                    (fun e1 ->
                       ((get_id e1) = id1) && (__proj__A__item__vis l e e1))
                    (__proj__A__item__l l))) (__proj__A__item__l l)
        then true
        else false
let rec union1 : 'op . 'op ae -> 'op ae -> (Prims.nat * 'op) Prims.list =
  fun l ->
    fun a ->
      match (l, a) with
      | (A (uu___, []), A (uu___1, [])) -> []
      | (A (uu___, x::xs), uu___1) -> x ::
          (union1 (A ((__proj__A__item__vis l), xs)) a)
      | (A (uu___, []), A (uu___1, x::xs)) -> x ::
          (union1 l (A ((__proj__A__item__vis a), xs)))
let union : 'op . 'op ae -> 'op ae -> 'op ae =
  fun l ->
    fun a ->
      A
        ((fun o ->
            fun o1 ->
              (((((FStar_List_Tot_Base.mem o (__proj__A__item__l l)) &&
                    (FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)))
                   && ((get_id o) <> (get_id o1)))
                  && (__proj__A__item__vis l o o1))
                 ||
                 ((((FStar_List_Tot_Base.mem o (__proj__A__item__l a)) &&
                      (FStar_List_Tot_Base.mem o1 (__proj__A__item__l a)))
                     && ((get_id o) <> (get_id o1)))
                    && (__proj__A__item__vis a o o1)))
                ||
                (((FStar_List_Tot_Base.mem o (__proj__A__item__l l)) &&
                    (FStar_List_Tot_Base.mem o1 (__proj__A__item__l a)))
                   && ((get_id o) <> (get_id o1)))), (union1 l a))
let rec absmerge1 :
  'op . 'op ae -> 'op ae -> 'op ae -> (Prims.nat * 'op) Prims.list =
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
let absmerge : 'op . 'op ae -> 'op ae -> 'op ae -> 'op ae =
  fun l ->
    fun a ->
      fun b ->
        A
          ((fun o ->
              fun o1 ->
                (((((((FStar_List_Tot_Base.mem o (__proj__A__item__l l)) &&
                        (FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)))
                       && ((get_id o) <> (get_id o1)))
                      && (__proj__A__item__vis l o o1))
                     ||
                     ((((FStar_List_Tot_Base.mem o (__proj__A__item__l a)) &&
                          (FStar_List_Tot_Base.mem o1 (__proj__A__item__l a)))
                         && ((get_id o) <> (get_id o1)))
                        && (__proj__A__item__vis a o o1)))
                    ||
                    ((((FStar_List_Tot_Base.mem o (__proj__A__item__l b)) &&
                         (FStar_List_Tot_Base.mem o1 (__proj__A__item__l b)))
                        && ((get_id o) <> (get_id o1)))
                       && (__proj__A__item__vis b o o1)))
                   ||
                   ((((FStar_List_Tot_Base.mem o (__proj__A__item__l l)) &&
                        (FStar_List_Tot_Base.mem o1 (__proj__A__item__l a)))
                       && ((get_id o) <> (get_id o1)))
                      && (__proj__A__item__vis (union l a) o o1)))
                  ||
                  ((((FStar_List_Tot_Base.mem o (__proj__A__item__l l)) &&
                       (FStar_List_Tot_Base.mem o1 (__proj__A__item__l b)))
                      && ((get_id o) <> (get_id o1)))
                     && (__proj__A__item__vis (union l b) o o1))),
            (absmerge1 l a b))

let sub_ae : 'op . ((Prims.nat * 'op) -> Prims.bool) -> 'op ae -> 'op ae =
  fun f ->
    fun l ->
      A
        ((fun o ->
            fun o1 ->
              (((((FStar_List_Tot_Base.mem o (__proj__A__item__l l)) &&
                    (FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)))
                   && ((get_id o) <> (get_id o1)))
                  && (__proj__A__item__vis l o o1))
                 && (f o))
                && (f o1)), (filter f (__proj__A__item__l l)))
let rec remove_op1 :
  'op . 'op ae -> (Prims.nat * 'op) -> (Prims.nat * 'op) Prims.list =
  fun tr ->
    fun x ->
      match __proj__A__item__l tr with
      | x1::xs ->
          if x = x1
          then xs
          else x1 :: (remove_op1 (A ((__proj__A__item__vis tr), xs)) x)
let remove_op : 'op . 'op ae -> (Prims.nat * 'op) -> 'op ae =
  fun tr ->
    fun x ->
      A
        ((fun o ->
            fun o1 ->
              (((FStar_List_Tot_Base.mem o (remove_op1 tr x)) &&
                  (FStar_List_Tot_Base.mem o1 (remove_op1 tr x)))
                 && ((get_id o) <> (get_id o1)))
                && (__proj__A__item__vis tr o o1)), (remove_op1 tr x))
type ('s, 'op, 'm) mrdt =
  {
  sim: 'op ae -> 's -> Prims.bool ;
  merge: 'op ae -> 's -> 'op ae -> 's -> 'op ae -> 's -> 's ;
  prop_merge: unit ;
  prop_oper: unit ;
  convergence: unit }
let __proj__Mkmrdt__item__sim :
  's 'op .
    ('s, 'op) datatype -> ('s, 'op, unit) mrdt -> 'op ae -> 's -> Prims.bool
  =
  fun m ->
    fun projectee ->
      match projectee with
      | { sim; merge; prop_merge; prop_oper; convergence;_} -> sim
let __proj__Mkmrdt__item__merge :
  's 'op .
    ('s, 'op) datatype ->
      ('s, 'op, unit) mrdt ->
        'op ae -> 's -> 'op ae -> 's -> 'op ae -> 's -> 's
  =
  fun m ->
    fun projectee ->
      match projectee with
      | { sim; merge; prop_merge; prop_oper; convergence;_} -> merge



let sim :
  's .
    unit ->
      ('s, Obj.t) datatype ->
        ('s, Obj.t, unit) mrdt -> Obj.t ae -> 's -> Prims.bool
  = fun op -> fun m -> fun d -> __proj__Mkmrdt__item__sim m d
let merge :
  's .
    unit ->
      ('s, Obj.t) datatype ->
        ('s, Obj.t, unit) mrdt ->
          Obj.t ae -> 's -> Obj.t ae -> 's -> Obj.t ae -> 's -> 's
  = fun op -> fun m -> fun d -> __proj__Mkmrdt__item__merge m d


