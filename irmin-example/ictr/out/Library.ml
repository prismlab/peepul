(* open Prims *)
let get_id : 'op . (int * 'op) -> int =
  fun uu___ -> match uu___ with | (id, uu___1) -> id
let get_op : 'op . (int * 'op) -> 'op =
  fun uu___ -> match uu___ with | (uu___1, op1) -> op1
let rec mem_id :
  'op . int -> (int * 'op) list -> bool =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id, uu___)::xs -> (n = id) || (mem_id n xs)
let rec unique_id : 'op . (int * 'op) list -> bool =
  fun l ->
    match l with
    | [] -> true
    | (id, uu___)::xs -> (Prims.op_Negation (mem_id id xs)) && (unique_id xs)
let rec get_eve :
  'op . int -> (int * 'op) list -> (int * 'op) =
  fun id ->
    fun l ->
      match l with
      | (id1, x)::xs -> if id = id1 then (id1, x) else get_eve id xs
type 'op ae =
  | A of ((int * 'op) -> (int * 'op) -> bool) * (int
  * 'op) list 
let uu___is_A : 'op . 'op ae -> bool = fun projectee -> true
let __proj__A__item__vis :
  'op . 'op ae -> (int * 'op) -> (int * 'op) -> bool =
  fun projectee -> match projectee with | A (vis, l) -> vis
let __proj__A__item__l : 'op . 'op ae -> (int * 'op) list =
  fun projectee -> match projectee with | A (vis, l) -> l
let abs_do : 'op . 'op ae -> (int * 'op) -> 'op ae =
  fun tr ->
    fun op1 ->
      A
        ((fun o ->
            fun o1 ->
              ((((FStar_List_Tot_Base.mem o (__proj__A__item__l tr)) &&
                   (FStar_List_Tot_Base.mem o1 (__proj__A__item__l tr)))
                  && ((get_id o) <> (get_id o1)))
                 && (__proj__A__item__vis tr o o1))
                ||
                (((FStar_List_Tot_Base.mem o (__proj__A__item__l tr)) &&
                    (o1 = op1))
                   && ((get_id o) <> (get_id op1)))), (op1 ::
          (__proj__A__item__l tr)))
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
let visib : 'op . int -> int -> 'op ae -> bool =
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
let rec union1 :
  'op .
    (int * 'op) list ->
      (int * 'op) list -> (int * 'op) list
  =
  fun l ->
    fun a ->
      match (l, a) with
      | ([], []) -> []
      | (x::xs, uu___) -> x :: (union1 xs a)
      | ([], uu___) -> a
let union : 'op . 'op ae -> 'op ae -> 'op ae =
  fun l ->
    fun a ->
      A
        ((fun o ->
            fun o1 ->
              ((((FStar_List_Tot_Base.mem o (__proj__A__item__l l)) &&
                   (FStar_List_Tot_Base.mem o1 (__proj__A__item__l l)))
                  && ((get_id o) <> (get_id o1)))
                 && (__proj__A__item__vis l o o1))
                ||
                ((((FStar_List_Tot_Base.mem o (__proj__A__item__l a)) &&
                     (FStar_List_Tot_Base.mem o1 (__proj__A__item__l a)))
                    && ((get_id o) <> (get_id o1)))
                   && (__proj__A__item__vis a o o1))),
          (union1 (__proj__A__item__l l) (__proj__A__item__l a)))
let rec abs_merge1 :
  'op .
    (int * 'op) list ->
      (int * 'op) list ->
        (int * 'op) list -> (int * 'op) list
  =
  fun l ->
    fun a ->
      fun b ->
        match (l, a, b) with
        | ([], [], []) -> []
        | (x::xs, uu___, uu___1) -> x :: (abs_merge1 xs a b)
        | ([], x::xs, uu___) -> x :: (abs_merge1 [] xs b)
        | ([], [], uu___) -> b
let abs_merge : 'op . 'op ae -> 'op ae -> 'op ae -> 'op ae =
  fun l ->
    fun a ->
      fun b ->
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
                  ((((FStar_List_Tot_Base.mem o (__proj__A__item__l b)) &&
                       (FStar_List_Tot_Base.mem o1 (__proj__A__item__l b)))
                      && ((get_id o) <> (get_id o1)))
                     && (__proj__A__item__vis b o o1))),
            (abs_merge1 (__proj__A__item__l l) (__proj__A__item__l a)
               (__proj__A__item__l b)))
let rec remove_op1 :
  'op . 'op ae -> (int * 'op) -> (int * 'op) list =
  fun tr ->
    fun x ->
      match __proj__A__item__l tr with
      | x1::xs ->
          if x = x1
          then xs
          else x1 :: (remove_op1 (A ((__proj__A__item__vis tr), xs)) x)
let remove_op : 'op . 'op ae -> (int * 'op) -> 'op ae =
  fun tr ->
    fun x ->
      A
        ((fun o ->
            fun o1 ->
              (((FStar_List_Tot_Base.mem o (remove_op1 tr x)) &&
                  (FStar_List_Tot_Base.mem o1 (remove_op1 tr x)))
                 && ((get_id o) <> (get_id o1)))
                && (__proj__A__item__vis tr o o1)), (remove_op1 tr x))

let get_st : 's 'rval . ('s * 'rval) -> 's =
  fun uu___ -> match uu___ with | (s1, r) -> s1
let get_rval : 's 'rval . ('s * 'rval) -> 'rval =
  fun uu___ -> match uu___ with | (s1, r) -> r
type ('s, 'op, 'rval) mrdt =
  {
  init: 's ;
  spec: (int * 'op) -> 'op ae -> 'rval ;
  sim: 'op ae -> 's -> bool ;
  pre_cond_do: 's -> (int * 'op) -> bool ;
  pre_cond_prop_do: 'op ae -> 's -> (int * 'op) -> bool ;
  pre_cond_merge: 's -> 's -> 's -> bool ;
  pre_cond_prop_merge:
    'op ae -> 's -> 'op ae -> 's -> 'op ae -> 's -> bool ;
  do1: 's -> (int * 'op) -> ('s * 'rval) ;
  merge: 's -> 's -> 's -> 's ;
  prop_do: unit ;
  prop_merge: unit ;
  prop_spec: unit ;
  convergence: unit }
let __proj__Mkmrdt__item__init : 's 'op 'rval . ('s, 'op, 'rval) mrdt -> 's =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> init
let __proj__Mkmrdt__item__spec :
  's 'op 'rval .
    ('s, 'op, 'rval) mrdt -> (int * 'op) -> 'op ae -> 'rval
  =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> spec
let __proj__Mkmrdt__item__sim :
  's 'op 'rval . ('s, 'op, 'rval) mrdt -> 'op ae -> 's -> bool =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> sim
let __proj__Mkmrdt__item__pre_cond_do :
  's 'op 'rval .
    ('s, 'op, 'rval) mrdt -> 's -> (int * 'op) -> bool
  =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> pre_cond_do
let __proj__Mkmrdt__item__pre_cond_prop_do :
  's 'op 'rval .
    ('s, 'op, 'rval) mrdt -> 'op ae -> 's -> (int * 'op) -> bool
  =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> pre_cond_prop_do
let __proj__Mkmrdt__item__pre_cond_merge :
  's 'op 'rval . ('s, 'op, 'rval) mrdt -> 's -> 's -> 's -> bool =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> pre_cond_merge
let __proj__Mkmrdt__item__pre_cond_prop_merge :
  's 'op 'rval .
    ('s, 'op, 'rval) mrdt ->
      'op ae -> 's -> 'op ae -> 's -> 'op ae -> 's -> bool
  =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> pre_cond_prop_merge
let __proj__Mkmrdt__item__do :
  's 'op 'rval .
    ('s, 'op, 'rval) mrdt -> 's -> (int * 'op) -> ('s * 'rval)
  =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> do1
let __proj__Mkmrdt__item__merge :
  's 'op 'rval . ('s, 'op, 'rval) mrdt -> 's -> 's -> 's -> 's =
  fun projectee ->
    match projectee with
    | { init; spec; sim; pre_cond_do; pre_cond_prop_do; pre_cond_merge;
        pre_cond_prop_merge; do1; merge; prop_do; prop_merge; prop_spec;
        convergence;_} -> merge




let init : 's . unit -> unit -> ('s, Obj.t, Obj.t) mrdt -> 's =
  fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__init d
let spec :
  's .
    unit ->
      unit ->
        ('s, Obj.t, Obj.t) mrdt -> (int * Obj.t) -> Obj.t ae -> Obj.t
  = fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__spec d
let sim :
  's .
    unit -> unit -> ('s, Obj.t, Obj.t) mrdt -> Obj.t ae -> 's -> bool
  = fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__sim d
let pre_cond_do :
  's .
    unit ->
      unit ->
        ('s, Obj.t, Obj.t) mrdt -> 's -> (int * Obj.t) -> bool
  = fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__pre_cond_do d
let pre_cond_prop_do :
  's .
    unit ->
      unit ->
        ('s, Obj.t, Obj.t) mrdt ->
          Obj.t ae -> 's -> (int * Obj.t) -> bool
  = fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__pre_cond_prop_do d
let pre_cond_merge :
  's .
    unit -> unit -> ('s, Obj.t, Obj.t) mrdt -> 's -> 's -> 's -> bool
  = fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__pre_cond_merge d
let pre_cond_prop_merge :
  's .
    unit ->
      unit ->
        ('s, Obj.t, Obj.t) mrdt ->
          Obj.t ae -> 's -> Obj.t ae -> 's -> Obj.t ae -> 's -> bool
  =
  fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__pre_cond_prop_merge d
let do1 :
  's .
    unit ->
      unit ->
        ('s, Obj.t, Obj.t) mrdt -> 's -> (int * Obj.t) -> ('s * Obj.t)
  = fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__do d
let merge :
  's . unit -> unit -> ('s, Obj.t, Obj.t) mrdt -> 's -> 's -> 's -> 's =
  fun op -> fun rval -> fun d -> __proj__Mkmrdt__item__merge d



