type var = string
type aexp = 
  | Int of int
  | Var of var
  | Plus of aexp * aexp
  | Mult of aexp * aexp 
  | Minus of aexp * aexp 
 
type bexp = 
  | True 
  | False
  | Eq of aexp * aexp 
  | Le of aexp * aexp 
  | Neg of bexp 
  | Conj of bexp * bexp 

type cmd = 
  | Assign of var * aexp 
  | Skip
  | Seq of cmd * cmd
  | If of bexp * cmd * cmd
  | While of bexp * cmd 

(* x:=1; y:=2; a:=x+y; b:=x-y *) 
let test1 = 
  Seq (Assign ("x", Int 1), 
    Seq (Assign ("y", Int 2), 
      Seq (Assign ("a", Plus  (Var "x", Var "y")), 
           Assign ("b", Minus (Var "x", Var "a")))))


(* x:=10; y:=2; while (x!=1) do (y:=y*x; x:=x-1) *)
let test2 = 
  Seq (Assign ("x", Int 10), 
    Seq (Assign("y", Int 2), 
         While (Neg (Eq (Var "x", Int 1)),
                Seq(Assign("y", Mult(Var "y", Var "x")), 
                    Assign("x", Minus(Var "x", Int 1))))))

(* a:=10; b:=2; q:=0; r:=a; while (b<=r) { r:=r-b; q:=q+1 } *)
let test3 = 
  Seq (Assign ("a", Int 10), 
    Seq (Assign ("b", Int 2), 
      Seq (Assign ("q", Int 0), 
        Seq (Assign ("r", Var "a"), 
           While (Le (Var "b", Var "r"),
                Seq(Assign("r", Minus(Var "r", Var "b")), 
                    Assign("q", Plus(Var "q", Int 1))))))))

module ABool = struct
  type t = Bot | Top | TT | FF
  let alpha b = if b then TT else FF

  (* partial order *)
  let order : t -> t -> bool 
  = fun b1 b2 ->
    if(b1=b2) then true
    else
      match b1, b2 with
      | Bot, _ -> true
      | _, Top -> true
      | _ -> false (* TODO *)

  (* least upper bound *)
  let lub : t -> t -> t 
  = fun b1 b2 ->
    if(b1=b2) then b1
    else
      match b1, b2 with
      | Bot, _ -> b2
      | _, Bot -> b1
      | Top, _ -> Top
      | _, Top -> Top
      | TT, FF -> Top
      | FF, TT -> Top

  (* abstract negation *)
  let neg : t -> t 
  = fun b ->
    match b with
    | TT -> FF
    | FF -> TT
    | _ -> b (* TODO *)

  (* abstract conjunction *)
  let conj : t -> t -> t
  = fun b1 b2 ->
    match b1, b2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | FF, _ -> FF
    | _, FF -> FF
    | Top, _ -> Top
    | _, Top -> Top
    | TT, TT -> TT (* TODO *)
end

module AValue = struct
  type t = Bot | Top | Neg | Zero | Pos | NonPos | NonZero | NonNeg
  let alpha : int -> t 
  =fun n -> if n = 0 then Zero else if n > 0 then Pos else Neg
  let to_string s = 
    match s with 
    | Bot -> "Bot" 
    | Top -> "Top" 
    | Pos -> "Pos" 
    | Neg -> "Neg" 
    | Zero -> "Zero"
    | NonNeg -> "NonNeg"
    | NonZero -> "NonZero"
    | NonPos -> "NonPos"

  (* partial order *)
  let order : t -> t -> bool
  = fun s1 s2 ->
    if(s1=s2) then true
    else
      match s1, s2 with
      | Bot, _ -> true
      | _, Top -> true
      | Pos, _ ->
        if(s2=NonNeg||s2=NonZero) then true else false
      | Neg, _ ->
        if(s2=NonZero||s2=NonPos) then true else false
      | Zero, _ ->
        if(s2=NonNeg||s2=NonPos) then true else false
      | _ -> false (* TODO *)

  (* least upper bound *)
  let lub : t -> t -> t 
  = fun s1 s2 ->
    if(s1=s2) then s1
    else
      match s1, s2 with
      | Bot, _ -> s2
      | _, Bot -> s1
      | _, Top -> Top
      | Top, _ -> Top
      | NonNeg, _ ->
        if(s2=Zero||s2=Pos) then NonNeg else Top
      | _, NonNeg ->
        if(s1=Zero||s1=Pos) then NonNeg else Top
      | Neg, _ ->
        if(s2=Zero||s2=NonPos) then NonPos else NonZero
      | _, Neg ->
        if(s1=Zero||s1=NonPos) then NonPos else NonZero
      | NonPos, _ ->
        if(s2=Zero) then NonPos else Top
      | _, NonPos ->
        if(s1=Zero) then NonPos else Top
      | Zero, Pos -> NonNeg
      | Zero, NonZero -> Top
      | Pos, Zero -> NonNeg
      | Pos, Neg -> NonZero
      | Pos, NonZero -> NonZero
      | NonZero, Zero -> Top
      | NonZero, Pos -> NonZero (* TODO *)
    
  (* abstract addition *)
  let plus : t -> t -> t 
  = fun a1 a2 ->
    match a1, a2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | _, Top -> Top
    | Top, _ -> Top
    | NonZero, _ ->
      if(a2=Zero) then NonZero else Top
    | _, NonZero ->
      if(a1=Zero) then NonZero else Top
    | Neg, _ ->
      if(a2=Pos||a2=NonNeg) then Top else Neg
    | _, Neg ->
      if(a1=Pos||a1=NonNeg) then Top else Neg
    | Pos, _ ->
      if(a2=NonPos) then Top else Pos
    | _, Pos ->
      if(a1=NonPos) then Top else Pos
    | NonPos, _ ->
      if(a2=NonNeg) then Top else NonPos
    | _, NonPos ->
      if(a1=NonNeg) then Top else NonPos
    | NonNeg, _ -> NonNeg
    | _, NonNeg -> NonNeg
    | Zero, Zero -> Zero (* TODO *)
     
  (* abstract multiplication *)
  let mult : t -> t -> t 
  = fun a1 a2 ->
    match a1, a2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | _, Top -> Top
    | Top, _ -> Top
    | Zero, _ -> Zero
    | _, Zero -> Zero
    | NonZero, _ ->
      if(a2=NonPos||a2=NonNeg) then Top else NonZero
    | _, NonZero ->
      if(a1=NonPos||a1=NonNeg) then Top else NonZero
    | NonPos, _ ->
      if(a2=Pos||a2=NonNeg) then NonPos else NonNeg
    | _, NonPos ->
      if(a1=Pos||a1=NonNeg) then NonPos else NonNeg
    | NonNeg, _ ->
      if(a2=Neg) then NonPos else NonNeg
    | _, NonNeg ->
      if(a1=Neg) then NonPos else NonNeg
    | Neg, Neg -> Pos
    | Neg, Pos -> Neg
    | Pos, Neg -> Neg
    | Pos, Pos -> Pos (* TODO *)

  (* abstract subtraction *)
  let minus : t -> t -> t
  = fun a1 a2 ->
    match a1, a2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | _, Top -> Top
    | Top, _ -> Top
    | Zero, _ -> a2
    | _, Zero -> a1
    | NonZero, _ -> Top
    | _, NonZero -> Top
    | NonNeg, _ ->
      if(a2=Neg) then Pos else Top
    | _, NonNeg ->
      if(a1=Neg) then Neg else Top
    | NonPos, Pos -> Neg
    | NonPos, _ -> Top
    | Pos, NonPos -> Pos
    | _, NonPos -> Top
    | Neg, Neg -> Top
    | Pos, Pos -> Top
    | Neg, Pos -> Neg
    | Pos, Neg -> Pos (* TODO *)
    
  let eq : t -> t -> ABool.t 
  = fun a1 a2 ->
    match a1, a2 with
    | Bot, _ -> ABool.Bot (* TODO *)
    | _, Bot -> ABool.Bot (* TODO *)
    | Zero, Zero -> ABool.TT
    | Neg, Zero -> ABool.FF
    | Neg, Pos -> ABool.FF
    | Neg, NonNeg -> ABool.FF
    | Zero, Neg -> ABool.FF
    | Zero, Pos -> ABool.FF
    | Zero, NonZero -> ABool.FF
    | Pos, Neg -> ABool.FF
    | Pos, Zero -> ABool.FF
    | Pos, NonPos -> ABool.FF
    | NonPos, Pos -> ABool.FF
    | NonZero, Zero -> ABool.FF
    | NonNeg, Neg -> ABool.FF
    | _ -> ABool.Top (* TODO *)

  let le : t -> t -> ABool.t 
  = fun a1 a2 ->
    match a1, a2 with
    | Bot, _ -> ABool.Bot (* TODO *)
    | _, Bot -> ABool.Bot (* TODO *)
    | Neg, Zero -> ABool.TT
    | Neg, Pos -> ABool.TT
    | Neg, NonNeg -> ABool.TT
    | Zero, Zero -> ABool.TT
    | Zero, Pos -> ABool.TT
    | Zero, NonNeg -> ABool.TT
    | Pos, Neg -> ABool.FF
    | Pos, Zero -> ABool.FF
    | Pos, NonPos -> ABool.FF
    | NonPos, Zero -> ABool.TT
    | NonPos, Pos -> ABool.TT
    | NonPos, NonNeg -> ABool.TT
    | NonNeg, Neg -> ABool.FF
    | _ -> ABool.Top (* TODO *)
end

module AState = struct
  module Map = Map.Make(struct type t = var let compare = compare end)
  type t = AValue.t Map.t (* var -> AValue.t map *)
  let bot = Map.empty
  let find x m = try Map.find x m with Not_found -> AValue.Bot
  let update x v m = Map.add x v m
  let update_join x v m = Map.add x (AValue.lub v (find x m)) m
  let order m1 m2 = Map.for_all (fun k v -> AValue.order v (find k m2)) m1
  let lub m1 m2 = Map.fold (fun k v m -> update_join k v m) m1 m2
  let print m = 
    Map.iter (fun k v -> 
   print_endline (k ^ " |-> " ^ AValue.to_string v)) m 
end

let rec aeval : aexp -> AState.t -> AValue.t
=fun a s ->
  match a with
  | Int n -> AValue.alpha n 
  | Var x -> AState.find x s 
  | Plus (a1, a2) -> AValue.plus (aeval a1 s) (aeval a2 s)
  | Mult (a1, a2) -> AValue.mult (aeval a1 s) (aeval a2 s)
  | Minus (a1, a2) -> AValue.minus (aeval a1 s) (aeval a2 s)

let rec beval : bexp -> AState.t -> ABool.t
=fun b s -> 
  match b with
  | True -> ABool.alpha true
  | False -> ABool.alpha false
  | Eq (a1, a2) -> AValue.eq (aeval a1 s) (aeval a2 s)
  | Le (a1, a2) -> AValue.le (aeval a1 s) (aeval a2 s)
  | Neg b -> ABool.neg (beval b s)
  | Conj (b1, b2) -> ABool.conj (beval b1 s) (beval b2 s)

let rec ceval : cmd -> AState.t -> AState.t
=fun c s -> 
  match c with
  | Assign (x, a) -> AState.update x (aeval a s) s
  | Skip -> s
  | Seq (c1,c2) -> ceval c2 (ceval c1 s)
  | If (b, c1, c2) -> 
      if beval b s = ABool.TT then (ceval c1 s)
      else if beval b s = ABool.FF then (ceval c2 s)
      else if beval b s = ABool.Bot then AState.bot
      else AState.lub (ceval c1 s) (ceval c2 s)

  | While (_, c) -> fix (ceval c) s

and fix f s0 = if AState.order (f s0) s0 then s0 else fix f (f s0)

let run : cmd -> AState.t
=fun c -> ceval c AState.bot

let _ = 
  let debug1 = AState.print (run test1);print_endline "" in
  let debug1 = AState.print (run test2);print_endline "" in
  AState.print (run test3)