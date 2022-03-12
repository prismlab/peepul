open Prims
type tree =
  | Leaf 
  | Node of (Prims.nat * Prims.nat) * tree * tree 
let (uu___is_Leaf : tree -> Prims.bool) =
  fun projectee -> match projectee with | Leaf -> true | uu___ -> false
let (uu___is_Node : tree -> Prims.bool) =
  fun projectee ->
    match projectee with | Node (_0, _1, _2) -> true | uu___ -> false
let (__proj__Node__item___0 : tree -> (Prims.nat * Prims.nat)) =
  fun projectee -> match projectee with | Node (_0, _1, _2) -> _0
let (__proj__Node__item___1 : tree -> tree) =
  fun projectee -> match projectee with | Node (_0, _1, _2) -> _1
let (__proj__Node__item___2 : tree -> tree) =
  fun projectee -> match projectee with | Node (_0, _1, _2) -> _2
let rec (memt1 : (Prims.nat * Prims.nat) -> tree -> Prims.bool) =
  fun x ->
    fun t ->
      match t with
      | Leaf -> false
      | Node (n, t1, t2) -> ((x = n) || (memt1 x t1)) || (memt1 x t2)
let rec (member_id : Prims.nat -> tree -> Prims.bool) =
  fun id ->
    fun t ->
      match t with
      | Leaf -> false
      | Node ((id1, uu___), t1, t2) ->
          ((id = id1) || (member_id id t1)) || (member_id id t2)
let rec (member_ele : Prims.nat -> tree -> Prims.bool) =
  fun ele ->
    fun t ->
      match t with
      | Leaf -> false
      | Node ((uu___, ele1), t1, t2) ->
          ((ele = ele1) || (member_ele ele t1)) || (member_ele ele t2)
let rec (forallt :
  ((Prims.nat * Prims.nat) -> Prims.bool) -> tree -> Prims.bool) =
  fun p ->
    fun t ->
      match t with
      | Leaf -> true
      | Node (n, t1, t2) -> ((p n) && (forallt p t1)) && (forallt p t2)
let rec (unique_id : tree -> Prims.bool) =
  fun t ->
    match t with
    | Leaf -> true
    | Node ((id, ele), t1, t2) ->
        (((((Prims.op_Negation (member_id id t1)) &&
              (Prims.op_Negation (member_id id t2)))
             &&
             (forallt
                (fun e ->
                   Prims.op_Negation
                     (member_id (FStar_Pervasives_Native.fst e) t2)) t1))
            &&
            (forallt
               (fun e ->
                  Prims.op_Negation
                    (member_id (FStar_Pervasives_Native.fst e) t1)) t2))
           && (unique_id t1))
          && (unique_id t2)
let rec (unique_ele : tree -> Prims.bool) =
  fun t ->
    match t with
    | Leaf -> true
    | Node ((id, ele), t1, t2) ->
        (((((Prims.op_Negation (member_ele ele t1)) &&
              (Prims.op_Negation (member_ele ele t2)))
             &&
             (forallt
                (fun e ->
                   Prims.op_Negation
                     (member_ele (FStar_Pervasives_Native.snd e) t2)) t1))
            &&
            (forallt
               (fun e ->
                  Prims.op_Negation
                    (member_ele (FStar_Pervasives_Native.snd e) t1)) t2))
           && (unique_ele t1))
          && (unique_ele t2)
let rec (is_bst : tree -> Prims.bool) =
  fun t ->
    match t with
    | Leaf -> true
    | Node (n, t1, t2) ->
        (((forallt
             (fun n' ->
                (FStar_Pervasives_Native.snd n) >
                  (FStar_Pervasives_Native.snd n')) t1)
            &&
            (forallt
               (fun n' ->
                  (FStar_Pervasives_Native.snd n) <
                    (FStar_Pervasives_Native.snd n')) t2))
           && (is_bst t1))
          && (is_bst t2)
let rec (size : tree -> Prims.nat) =
  fun t1 ->
    match t1 with
    | Leaf -> Prims.int_zero
    | Node (uu___, t11, t2) -> (Prims.int_one + (size t11)) + (size t2)
type t = tree

let rec (memt : (Prims.nat * Prims.nat) -> t -> Prims.bool) =
  fun x ->
    fun t1 ->
      match t1 with
      | Leaf -> false
      | Node (n, t11, t2) ->
          if x = n
          then true
          else
            if
              (FStar_Pervasives_Native.snd x) <
                (FStar_Pervasives_Native.snd n)
            then memt x t11
            else memt x t2
let (ge : (Prims.nat * Prims.nat) -> (Prims.nat * Prims.nat) -> Prims.bool) =
  fun n1 ->
    fun n2 ->
      (((FStar_Pervasives_Native.snd n1) > (FStar_Pervasives_Native.snd n2))
         &&
         ((FStar_Pervasives_Native.fst n1) <>
            (FStar_Pervasives_Native.fst n2)))
        || (n1 = n2)
let rec (find_max : tree -> (Prims.nat * Prims.nat)) =
  fun t1 ->
    match t1 with
    | Node (v, uu___, t2) ->
        (match t2 with | Leaf -> v | uu___1 -> find_max t2)
let rec (delete_ele : Prims.nat -> t -> t) =
  fun x ->
    fun tr ->
      match tr with
      | Leaf -> Leaf
      | Node (n, t1, t2) ->
          if (FStar_Pervasives_Native.snd n) = x
          then
            (match (t1, t2) with
             | (Leaf, Leaf) -> Leaf
             | (uu___, Leaf) -> t1
             | (Leaf, uu___) -> t2
             | uu___ ->
                 let y = find_max t1 in
                 Node
                   (y, (delete_ele (FStar_Pervasives_Native.snd y) t1), t2))
          else
            if x < (FStar_Pervasives_Native.snd n)
            then Node (n, (delete_ele x t1), t2)
            else Node (n, t1, (delete_ele x t2))
let rec (delete : (Prims.nat * Prims.nat) -> t -> t) =
  fun x ->
    fun tr ->
      match tr with
      | Leaf -> Leaf
      | Node (n, t1, t2) ->
          if n = x
          then
            (match (t1, t2) with
             | (Leaf, Leaf) -> Leaf
             | (uu___, Leaf) -> t1
             | (Leaf, uu___) -> t2
             | uu___ -> let y = find_max t1 in Node (y, (delete y t1), t2))
          else
            if
              (FStar_Pervasives_Native.snd x) <
                (FStar_Pervasives_Native.snd n)
            then Node (n, (delete x t1), t2)
            else Node (n, t1, (delete x t2))
let rec (update : Prims.nat -> Prims.nat -> t -> tree) =
  fun ele ->
    fun id ->
      fun tr ->
        match tr with
        | Leaf -> Node ((id, ele), Leaf, Leaf)
        | Node ((id1, ele1), t1, t2) ->
            if ele = ele1
            then Node ((id, ele1), t1, t2)
            else
              if ele < ele1
              then Node ((id1, ele1), (update ele id t1), t2)
              else Node ((id1, ele1), t1, (update ele id t2))
let (app_op : t -> Orset_opt.o -> t) =
  fun s1 ->
    fun op ->
      if Orset_opt.opa op
      then update (Orset_opt.get_ele op) (Orset_opt.get_id op) s1
      else delete_ele (Orset_opt.get_ele op) s1
let rec (insert : (Prims.nat * Prims.nat) -> t -> tree) =
  fun x ->
    fun t1 ->
      match t1 with
      | Leaf -> Node (x, Leaf, Leaf)
      | Node (n, t11, t2) ->
          if x = n
          then t1
          else
            if
              (FStar_Pervasives_Native.snd x) <
                (FStar_Pervasives_Native.snd n)
            then (let y = insert x t11 in Node (n, (insert x t11), t2))
            else Node (n, t11, (insert x t2))
let rec (totree1 : Orset_opt.s -> t -> t) =
  fun l ->
    fun acc -> match l with | [] -> acc | x::xs -> totree1 xs (insert x acc)
let (totree : Orset_opt.s -> t) = fun l -> totree1 l Leaf
let (lt : (Prims.nat * Prims.nat) -> (Prims.nat * Prims.nat) -> Prims.bool) =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((id, ele), (id1, ele1)) -> (ele < ele1) && (id <> id1)
let rec (appendt : Orset_opt.s -> Orset_opt.s -> Orset_opt.s) =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], []) -> []
      | (x::xs, uu___) -> x :: (appendt xs l2)
      | ([], uu___) -> l2
let rec (flatten : t -> Orset_opt.s) =
  fun t1 ->
    match t1 with
    | Leaf -> []
    | Node (n, t11, t2) -> n :: (appendt (flatten t11) (flatten t2))
let (fst : (Prims.nat * Prims.nat) -> Prims.nat) =
  fun uu___ -> match uu___ with | (id, ele) -> id
let (snd : (Prims.nat * Prims.nat) -> Prims.nat) =
  fun uu___ -> match uu___ with | (id, ele) -> ele
let (sim : Orset_opt.ae -> t -> Prims.bool) =
  fun tr ->
    fun s1 ->
      let lsta =
        Orset_opt.filter (fun a -> Orset_opt.opa a)
          (Orset_opt.__proj__A__item__l tr) in
      let lstr =
        Orset_opt.filter (fun r -> Orset_opt.opr r)
          (Orset_opt.__proj__A__item__l tr) in
      let lst =
        Orset_opt.filter
          (fun a ->
             Prims.op_Negation
               (Orset_opt.existsb
                  (fun r ->
                     (((Orset_opt.get_id a) <> (Orset_opt.get_id r)) &&
                        ((Orset_opt.get_ele r) = (Orset_opt.get_ele a)))
                       && (Orset_opt.__proj__A__item__vis tr a r)) lstr))
          lsta in
      (forallt
         (fun e ->
            (Orset_opt.forallb (fun a -> (fst e) >= (Orset_opt.get_id a))
               (Orset_opt.filter (fun a -> (Orset_opt.get_ele a) = (snd e))
                  lst))
              &&
              ((FStar_List_Tot_Base.mem ((fst e), (Orset_opt.Add (snd e)))
                  (Orset_opt.__proj__A__item__l tr))
                 &&
                 (Prims.op_Negation
                    (Orset_opt.existsb
                       (fun r ->
                          ((fst e) <> (Orset_opt.get_id r)) &&
                            (Orset_opt.__proj__A__item__vis tr
                               ((fst e), (Orset_opt.Add (snd e))) r))
                       (Orset_opt.filter
                          (fun r -> (snd e) = (Orset_opt.get_ele r)) lstr)))))
         s1)
        &&
        (Orset_opt.forallb (fun a -> member_ele (Orset_opt.get_ele a) s1) lst)
let (diff : t -> t -> t) =
  fun a -> fun l -> totree (Orset_opt.diff (flatten a) (flatten l))
(* let (merge : *)
(*   Orset_opt.ae -> t -> Orset_opt.ae -> t -> Orset_opt.ae -> t -> t) = *)
(*   fun ltr -> *)
(*     fun l -> *)
(*       fun atr -> *)
(*         fun a -> *)
(*           fun btr -> *)
(*             fun b -> *)
(*               let m = *)
(*                 Orset_opt.merge ltr (flatten l) atr (flatten a) btr *)
(*                   (flatten b) in *)
(*               totree m *)

let (merge1 : t ->  t -> t -> t) =
  fun l ->
  fun a ->
  fun b ->
  let m =
    Orset_opt.merge1 (flatten l) (flatten a) (flatten b) in
  totree m

let (max : Prims.int -> Prims.int -> Prims.int) =
  fun n1 -> fun n2 -> if n1 > n2 then n1 else n2
let rec (pos : Orset_opt.s -> (Prims.nat * Prims.nat) -> Prims.nat) =
  fun l ->
    fun e ->
      match l with
      | x::y -> if x = e then Prims.int_zero else Prims.int_one + (pos y e)
let rec (sorted : Orset_opt.s -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | x::[] -> true
    | x::y::xs -> ((snd x) < (snd y)) && (sorted (y :: xs))
let rec (take_element : Orset_opt.s -> Prims.nat -> Orset_opt.s) =
  fun l ->
    fun n ->
      match l with
      | h::t1 ->
          if n > Prims.int_zero
          then take_element t1 (n - Prims.int_one)
          else [h]
let (takemiddle : Orset_opt.s -> Orset_opt.s) =
  fun l ->
    take_element l ((FStar_List_Tot_Base.length l) / (Prims.of_int (2)))
let rec (take : Prims.nat -> Orset_opt.s -> Orset_opt.s) =
  fun n ->
    fun l ->
      if n = Prims.int_zero
      then []
      else (match l with | h::t1 -> h :: (take (n - Prims.int_one) t1))

let (takefront : Orset_opt.s -> Orset_opt.s) =
  fun l ->
    let t1 = take ((FStar_List_Tot_Base.length l) / (Prims.of_int (2))) l in
    t1
let rec (drop : Prims.nat -> Orset_opt.s -> Orset_opt.s) =
  fun n ->
    fun l ->
      if n = Prims.int_zero
      then l
      else (match l with | h::t1 -> drop (n - Prims.int_one) t1)
let (takeback : Orset_opt.s -> Orset_opt.s) =
  fun l ->
    drop
      (((FStar_List_Tot_Base.length l) / (Prims.of_int (2))) + Prims.int_one)
      l
let rec (tree_of_list : Orset_opt.s -> tree) =
  fun l ->
    match l with
    | [] -> Leaf
    | h::[] -> Node (h, Leaf, Leaf)
    | h::t1 ->
        Node
          ((FStar_List_Tot_Base.hd (takemiddle l)),
            (tree_of_list (takefront l)), (tree_of_list (takeback l)))
