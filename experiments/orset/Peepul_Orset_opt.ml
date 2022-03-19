open Prims
type op =
  | Add of Prims.nat 
  | Rem of Prims.nat 
  | Look of Prims.nat 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add _0 -> true | uu___ -> false
let (__proj__Add__item___0 : op -> Prims.nat) =
  fun projectee -> match projectee with | Add _0 -> _0
let (uu___is_Rem : op -> Prims.bool) =
  fun projectee -> match projectee with | Rem _0 -> true | uu___ -> false
let (__proj__Rem__item___0 : op -> Prims.nat) =
  fun projectee -> match projectee with | Rem _0 -> _0
type o = (Prims.nat * op)
let (get_id : o -> Prims.nat) =
  fun uu___ -> match uu___ with | (id, uu___1) -> id
let (opa : o -> Prims.bool) =
  fun o1 ->
    match o1 with
    | (uu___, Add uu___1) -> true
    | (uu___, Rem uu___1) -> false
let (opr : o -> Prims.bool) =
  fun o1 ->
    match o1 with
    | (uu___, Add uu___1) -> false
    | (uu___, Rem uu___1) -> true
let (get_ele : o -> Prims.nat) =
  fun o1 -> match o1 with | (uu___, Add ele) -> ele | (uu___, Rem ele) | (uu___, Look ele) -> ele
let rec (member_id :
  Prims.nat -> (Prims.nat * Prims.nat) Prims.list -> Prims.bool) =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id, uu___)::xs -> (n = id) || (member_id n xs)
let rec (member_ele :
  Prims.nat -> (Prims.nat * Prims.nat) Prims.list -> Prims.bool) =
  fun ele ->
    fun l ->
      match l with
      | [] -> false
      | (uu___, ele1)::xs -> (ele = ele1) || (member_ele ele xs)
let rec (unique_id : (Prims.nat * Prims.nat) Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | (id, uu___)::xs ->
        (Prims.op_Negation (member_id id xs)) && (unique_id xs)
let rec (unique_ele : (Prims.nat * Prims.nat) Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | (uu___, ele)::xs ->
        (Prims.op_Negation (member_ele ele xs)) && (unique_ele xs)
type s = (Prims.nat * Prims.nat) Prims.list
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
let rec except : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl ->
          if Prims.op_Negation (f hd)
          then hd :: (except f tl)
          else except f tl

let rec (update : s -> Prims.nat -> Prims.nat -> s) =
  fun s1 ->
    fun ele ->
      fun id ->
        match s1 with
        | [] -> []
        | (id1, ele1)::xs ->
            if ele = ele1
            then (id, ele1) :: xs
            else (id1, ele1) :: (update xs ele id)
let rec (remove_ele : s -> Prims.nat -> s) =
  fun s1 ->
    fun ele ->
      match s1 with
      | [] -> []
      | (id1, ele1)::xs ->
          if ele = ele1 then xs else (id1, ele1) :: (remove_ele xs ele)
let (app_op : s -> o -> s) =
  fun s1 ->
    fun op1 ->
      if opa op1
      then
        (if member_ele (get_ele op1) s1
         then update s1 (get_ele op1) (get_id op1)
         else ((get_id op1), (get_ele op1)) :: s1)
      else (if opr op1 then
        (if member_ele (get_ele op1) s1
        then remove_ele s1 (get_ele op1)
        else s1) else (if member_ele (get_ele op1) s1 then s1 else s1))
let rec (member : Prims.nat -> o Prims.list -> Prims.bool) =
  fun n ->
    fun l ->
      match l with
      | [] -> false
      | (id, uu___)::xs -> (n = id) || (member n xs)
let rec (unique : o Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | (id, uu___)::xs -> (Prims.op_Negation (member id xs)) && (unique xs)
type ae =
  | A of (o -> o -> Prims.bool) * o Prims.list 
let (uu___is_A : ae -> Prims.bool) = fun projectee -> true
let (__proj__A__item__vis : ae -> o -> o -> Prims.bool) =
  fun projectee -> match projectee with | A (vis, l) -> vis
let (__proj__A__item__l : ae -> o Prims.list) =
  fun projectee -> match projectee with | A (vis, l) -> l
let (fst : (Prims.nat * Prims.nat) -> Prims.nat) =
  fun uu___ -> match uu___ with | (id, ele) -> id
let (snd : (Prims.nat * Prims.nat) -> Prims.nat) =
  fun uu___ -> match uu___ with | (id, ele) -> ele
let (sim : ae -> s -> Prims.bool) =
  fun tr ->
    fun s1 ->
      let lsta = filter (fun a -> opa a) (__proj__A__item__l tr) in
      let lstr = filter (fun r -> opr r) (__proj__A__item__l tr) in
      let lst =
        filter
          (fun a ->
             Prims.op_Negation
               (existsb
                  (fun r ->
                     (((get_id a) <> (get_id r)) &&
                        ((get_ele r) = (get_ele a)))
                       && (__proj__A__item__vis tr a r)) lstr)) lsta in
      (forallb
         (fun e ->
            (forallb (fun a -> (fst e) >= (get_id a))
               (filter (fun a -> (get_ele a) = (snd e)) lst))
              &&
              ((FStar_List_Tot_Base.mem ((fst e), (Add (snd e)))
                  (__proj__A__item__l tr))
                 &&
                 (Prims.op_Negation
                    (existsb
                       (fun r ->
                          ((fst e) <> (get_id r)) &&
                            (__proj__A__item__vis tr ((fst e), (Add (snd e)))
                               r))
                       (filter (fun r -> (snd e) = (get_ele r)) lstr))))) s1)
        && (forallb (fun a -> member_ele (get_ele a) s1) lst)
let rec (union1 : ae -> ae -> o Prims.list) =
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
let rec (absmerge1 : ae -> ae -> ae -> o Prims.list) =
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
let rec (remove : s -> (Prims.nat * Prims.nat) -> s) =
  fun l ->
    fun ele ->
      match l with
      | [] -> []
      | x::xs -> if x = ele then xs else x :: (remove xs ele)
let rec (diff : s -> s -> s) =
  fun a ->
    fun l ->
      match (a, l) with
      | (uu___, []) -> a
      | (uu___, x::xs) ->
          if FStar_List_Tot_Base.mem x a
          then diff (remove a x) xs
          else diff a xs
let rec (get_node : s -> Prims.nat -> (Prims.nat * Prims.nat)) =
  fun l ->
    fun ele ->
      match l with
      | (id1, ele1)::xs ->
          if ele = ele1 then (id1, ele1) else get_node xs ele
let rec (unionst : s -> s -> s) =
  fun a ->
    fun b ->
      match (a, b) with
      | ([], []) -> []
      | (x::xs, uu___) -> x :: (unionst xs b)
      | uu___ -> b

let rec merge1 l a b =
   match l,a,b with
   |[],[],[] -> []
   |x::xs, _, _ -> if (FStar_List_Tot_Base.mem x a && FStar_List_Tot_Base.mem x b) then x::(merge1 xs (remove a x) (remove b x))
                    else if FStar_List_Tot_Base.mem x a then merge1 xs (remove a x) b
                      else if FStar_List_Tot_Base.mem x b then merge1 xs a (remove b x)
                        else (merge1 xs a b)

   |[], (id,ele)::xs, _ -> if (not (member_ele ele b)) then (id,ele)::(merge1 [] xs b)
                            else (let b1 = (get_node b ele) in (if id > fst b1 then (id,ele)::(merge1 [] xs (remove b b1))
                               else (merge1 [] xs b)))

   |[],[],_ -> b

(* let (merge1 : s -> s -> s -> s) = *)
(*   fun l -> *)
(*     fun a -> *)
(*       fun b -> *)
(*         let i = *)
(*           filter *)
(*             (fun e -> *)
(*                (FStar_List_Tot_Base.mem e a) && (FStar_List_Tot_Base.mem e b)) *)
(*             l in *)
(*         let la = diff a l in *)
(*         let lb = diff b l in *)
(*         let la1 = *)
(*           filter *)
(*             (fun e -> *)
(*                (member_ele (snd e) la) && *)
(*                  (Prims.op_Negation (member_ele (snd e) lb))) la in *)
(*         let lb1 = *)
(*           filter *)
(*             (fun e -> *)
(*                (member_ele (snd e) lb) && *)
(*                  (Prims.op_Negation (member_ele (snd e) la))) lb in *)
(*         let la2 = *)
(*           filter *)
(*             (fun e -> *)
(*                ((member_ele (snd e) la) && (member_ele (snd e) lb)) && *)
(*                  ((fst (get_node a (snd e))) > (fst (get_node b (snd e))))) *)
(*             la in *)
(*         let lb2 = *)
(*           filter *)
(*             (fun e -> *)
(*                ((member_ele (snd e) la) && (member_ele (snd e) lb)) && *)
(*                  ((fst (get_node b (snd e))) > (fst (get_node a (snd e))))) *)
(*             lb in *)
(*         let u1 = unionst i la1 in *)
(*         let u2 = unionst u1 lb1 in let u3 = unionst u2 la2 in unionst u3 lb2 *)
