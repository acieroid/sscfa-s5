let stats = BatHashtbl.create 20

let called name () =
  match BatHashtbl.Exceptionless.find stats  name with
  | Some v -> BatHashtbl.replace stats name (1+v)
  | None -> BatHashtbl.add stats name 1

let print () =
  print_endline "Function calls: ";
  let cmp (_, x) (_, y) = - (Pervasives.compare x y) in
  let vals = BatList.sort cmp (BatList.of_enum (BatHashtbl.enum stats)) in
  BatList.iter (fun (name, count) -> Printf.printf "%s: %d\n" name count) vals
