let rec op_At (l1 : 'a list) (l2 : 'a list) : 'a list =
  match l1 with
  | [] -> l2
  | x :: xs -> x :: op_At xs l2

let rev (xs: 'a list) : 'a list = 
  let rec go acc = 
    function
    | [] -> acc 
    | hd::tl -> go (hd::acc) tl 
  in go [] xs