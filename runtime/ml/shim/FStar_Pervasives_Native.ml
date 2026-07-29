type 'a option = 'a Stdlib.Option.t = None | Some of 'a

let uu___is_Some : 'a option -> bool = 
  function
  | Some _ -> true
  | _ -> false