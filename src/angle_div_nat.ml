let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a);;

let rec seq i n =
  if n = 0 then []
  else i :: seq (i + 1) (n - 1);;

let u n i = float (pow 2 i / n) /. (2. ** float i);;

let i = 4;;
float (pow 2 (i + 2) / 3) *. (3. /. float (pow 2 (i + 2)));;

List.map (fun i -> 3. *. u 3 i, 4. *. u 4 i) (seq 0 20);;
List.map (fun i -> (1. -. 4. *. u 4 i, 1. -. 3. *. u 3 i)) (seq 0 20);;
List.map (fun i -> 3. *. u 3 i, 4. *. u 4 i) (seq 0 40);;
