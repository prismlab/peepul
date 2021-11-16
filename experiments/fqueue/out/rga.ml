
let _ = Random.self_init ()

let stream = (Stream.from (fun n -> Some (Z.of_int (n + 1))))

let random x = Z.of_int (Random.int x)

let next_id () = Stream.next stream

let pick_r r r1 r2 = if (Random.int 100 < r) then r1 else r2

let rec gen_list acc x =
  if x = 0 then acc else
    gen_list (acc @ [(next_id (), ref (Some (random 1000)))]) (x-1)

let insert value rga =
  rga @ [(next_id (), ref (Some value))]

let rec remove rga = match rga with
  | [] -> []
  | x::xs -> if !(snd x) = None then remove xs else ((fst x), ref None)::xs

let rec checkNull idx a = match a with
  | [] -> false
  | x::xs -> if (fst x) = idx then (if !(snd x) = None then true else false) else checkNull idx xs

let rec merge lca a b = match lca with
  | [] -> List.merge (Stdlib.compare) a b
  | x::xs -> let () = (if checkNull (fst x) a || checkNull (fst x) b then (snd x) := None else ()) in merge xs a b

let app_op rga r = if (Random.int 100 < r) then (insert (random 10000) rga) else
    (remove rga)

let rec test lca a b count =
  if count = 0 then (lca, a, b) else
    let lca = merge lca a b in
    let replica_ratio = 50 in
    let insert_ratio = 50 in
    let merge_ratio = 500 in
    let (a, b) = if pick_r replica_ratio a b = a then (app_op a insert_ratio, b) else (a, app_op b insert_ratio) in
    let lca = if (count mod merge_ratio = 0) then merge lca a b else lca in
    test lca a b (count-1)

let _ =
  let lca = gen_list [] 10000 in
  let a = lca in
  let b = lca in
  let (lca, a, b) = test lca a b 10000 in
  ()

