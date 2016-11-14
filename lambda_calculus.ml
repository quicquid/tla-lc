open Format

type tp = Ti | To | Arr of tp * tp

let pp_wrap condition pp_fmt fmt x=
  if condition then
    fprintf fmt "(%a)" pp_fmt x
  else
    fprintf fmt "%a" pp_fmt x

let rec pp_type ?inside:(ins=false) fmt = function
  | Ti -> fprintf fmt "i"
  | To -> fprintf fmt "o"
  | Arr(t1, t2) ->
    fprintf fmt "%a>%a" (pp_wrap ins pp_type) t1 (pp_wrap ins pp_type) t2


module ID : sig
  type t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val make : string -> tp -> t
  val copy : t -> t
  val name : t -> string
  val ty : t -> tp
  val pp : Format.formatter -> t -> unit
end = struct
  type t = {
    name: string;
    id: int;
    ty: tp
  }

  let equal a b = a.id = b.id
  let compare a b = Pervasives.compare a.id b.id
  let make =
    let n = ref 0 in
    fun name ty ->
      let res = {name; ty; id= !n} in
      incr n;
      res

  let copy {name; ty; _} = make name ty
  let name id = id.name
  let ty id = id.ty
  let pp out {name; ty; id} =
    fprintf out "%s:%a" name (pp_type ~inside:false) ty
end

module IDMap = Map.Make(ID)

type expr = {
  expr: expr_cell;
  ty: tp
}
and expr_cell =
  | Const of ID.t
  | Var of ID.t
  | App of expr * expr
  | Abs of ID.t * expr
  | Mu of ID.t * expr

type subst = expr IDMap.t

let (-->) x y = Arr (x, y)

let etype t = t.ty

let const id = {expr=Const id; ty=ID.ty id}
let var id = {expr=Var id; ty=ID.ty id}
let app s t =
  let ty = match s.ty, t.ty with
    | Arr (x,y), z when x = z -> y
    | Arr (x,y), _ ->
      failwith "Types in app don't fit."
    | _, _ ->
        failwith "First type in app must be an arrow."
  in
  { expr=App(s,t); ty }
let app_l = List.fold_left app
let mu x t =
  assert (ID.ty x = t.ty);
  { expr=Mu (x,t); ty=t.ty }

let abs (v:ID.t) e =
  {expr=Abs(v,e); ty= (ID.ty v --> e.ty) }

let abs_l = List.fold_right abs

let rec subst (s:subst) (t:expr): expr = match t.expr with
  | Const _ -> t
  | Var id ->
    begin
      try IDMap.find id s
      with Not_found -> t
    end
  | App (e, f) ->
    app (subst s e) (subst s f)
  | Abs (id, e) ->
    let id' = ID.copy id in
    let s' = IDMap.add id (var id') s in
    abs id' (subst s' e)
  | Mu (id, e) ->
    let id' = ID.copy id in
    let s' = IDMap.add id (var id') s in
    mu id' (subst s' e)

type eval_mode =
  | SNF
  | WHNF

(* Strong Normal Form *)
let reduce t =
  let rec aux mode s t = match t.expr with
    | Const _ -> t
    | Var _ -> subst s t
    | App (f, arg) ->
      let f = aux WHNF s f in
      begin match f.expr, mode with
        | Abs (v, body), _ ->
          let arg = aux mode s arg in
          aux mode (IDMap.add v arg s) body
        | _, WHNF ->
          let arg = subst s arg in
          app f arg
        | _, SNF ->
          let arg = aux mode s arg in
          app f arg
      end
    | Abs (id, e) ->
      begin match mode with
        | WHNF -> subst s t
        | SNF ->
          let id' = ID.copy id in
          let s' = IDMap.add id (var id') s in
          abs id' (aux mode s' e)
      end
    | Mu (id, e) ->
      begin match mode with
        | WHNF -> subst s t
        | SNF ->
          let id' = ID.copy id in
          let s' = IDMap.add id (var id') s in
          mu id' (aux mode s' e)
      end
  in
  aux SNF IDMap.empty t

module IDPairSet = Set.Make(struct
    type t = ID.t * ID.t
    let compare (i1,j1) (i2,j2) =
      let c = ID.compare i1 i2 in
      if c<> 0 then c else ID.compare j1 j2
  end)

(* alpha-equivalence *)
let alpha_eq (a:expr)(b:expr): bool =
  let rec aux (pairs:IDPairSet.t) (s:subst) a b =
    match a.expr, b.expr with
      | Var v1, Var v2 when IDPairSet.mem (v1,v2) pairs -> true (* corecursion *)
      | Var v, _ when IDMap.mem v s ->
        aux pairs s (IDMap.find v s) b
      | _, Var v when IDMap.mem v s ->
        aux pairs s a (IDMap.find v s)
      | Var v1, Var v2 -> ID.equal v1 v2
      | Const v1, Const v2 -> ID.equal v1 v2
      | App (f1,arg1), App (f2,arg2) ->
        aux pairs s f1 f2 && aux pairs s arg1 arg2
      | Abs (x1, body1), Abs (x2, body2) ->
        let pairs' = IDPairSet.add (x1,x2) pairs in
        aux pairs' s body1 body2
      | Mu (x1, body1), Mu (x2, body2) ->
        (* assume, from now on, x1==x2 *)
        let pairs' = IDPairSet.add (x1,x2) pairs in
        let s' = s |> IDMap.add x1 a |> IDMap.add x2 b in
        aux pairs' s' body1 body2
      | Mu (x, body), _ ->
        (* expand *)
        let s' = IDMap.add x a s in
        aux pairs s' body b
      | _, Mu (x, body) ->
        (* expand *)
        let s' = IDMap.add x b s in
        aux pairs s' a body
      | Var _, _
      | Const _, _
      | App _, _
      | Abs _, _ -> false
  in
  aux IDPairSet.empty IDMap.empty a b

let pp_cond conditon pp_fmt fmt x =
  if conditon then
    fprintf fmt "%a" pp_fmt x
  else
    ()

let pp_term fmt term =
  let rec pp_term_ inside fmt t = match t.expr with
    | Const id
    | Var id -> ID.pp fmt id
    | App (s,t) ->
      fprintf fmt "%a "
        (pp_wrap inside (pp_term_ true)) s;
      fprintf fmt "%a"
        (pp_wrap inside (pp_term_ true)) t
    | Abs (id,t) ->
      fprintf fmt "\\%a %a" ID.pp id
        (pp_wrap inside (pp_term_ true)) t
    | Mu (id,t) ->
      fprintf fmt "@<1>µ%a %a" ID.pp id
        (pp_wrap inside (pp_term_ true)) t
  in
  pp_term_ false fmt term

(* test terms *)
module T = struct
  let a = const (ID.make "a" Ti)
  let b = const (ID.make "b" Ti)
  let c = const (ID.make "c" Ti)
  let f = const (ID.make "f" (Ti --> Ti))
  let x = ID.make "x" Ti
  let y = ID.make "y" (Ti --> Ti)
  let z = ID.make "z" Ti
  let z' = ID.copy z

  let e1 = abs x (var z)
  let e2 = abs z (app (abs x (abs z' (var x))) (var z))

  let zero = ID.make "zero" Ti
  let succ = ID.make "succ" (Ti --> Ti)

  let ty_church = (Ti --> Ti) --> (Ti --> Ti)

  let church (n:int): expr =
    let rec aux n =
      if n=0 then var zero
      else app (var succ) (aux (n-1))
    in
    abs_l [succ; zero] (aux n)

  let plus =
    let m = ID.make "m" ty_church in
    let n = ID.make "n" ty_church in
    abs_l [m; n; succ; zero]
      (app_l (var m) [var succ; app_l (var n) [var succ; var zero]])

  let product =
    let m = ID.make "m" ty_church in
    let n = ID.make "n" ty_church in
    abs_l [m; n; succ; zero]
      (app_l (var m) [app (var n) (var succ); var zero])

  (* compute [a * b] efficiently! *)
  let product_compute a b = app_l product [church a; church b]

  let t_10_000 = product_compute 100 100 |> reduce

  let cycle n =
    app (abs y (mu x (app (var y) (var x)))) (app (church n) f)
    |> reduce

  let cycle1 = cycle 1
  let cycle2 = cycle 2
  let cycle3 = cycle 3
end

let () =
  List.iter
    (fun (t1,t2,expect) ->
       let tostr b = if b then "EQ" else "NEQ" in
       let res = alpha_eq (reduce t1) (reduce t2) in
       Format.printf "@[<v2>%s (expect %s)@ (@[%a@])@ (@[%a@])@]@."
         (tostr res) (tostr expect) pp_term t1 pp_term t2)
    [ T.cycle1, T.cycle1, true;
      T.cycle2, T.cycle3, true;
      T.product_compute 2 2, T.cycle2, false;
      T.product_compute 2 2, T.church 4, true;
      T.product_compute 2 2, T.church 5, false;
      T.product_compute 10 10, T.church 100, true;
    ]