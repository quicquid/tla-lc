open Format

type tp = Tt | Ti | To | Arr of tp * tp

let pp_wrap condition pp_fmt fmt x=
  if condition then
    fprintf fmt "(%a)" pp_fmt x
  else
    fprintf fmt "%a" pp_fmt x

let rec pp_type ?inside:(ins=false) fmt = function
  | Ti -> fprintf fmt "i"
  | To -> fprintf fmt "o"
  | Tt -> fprintf fmt "t"
  | Arr(t1, t2) ->
    let pp_ty = pp_type ~inside:true in
    match ins with
    | false  -> fprintf fmt "%a>%a" pp_ty t1 pp_ty t2
    | true -> fprintf fmt "(%a>%a)" pp_ty t1 pp_ty t2

let pp_ty = pp_type ~inside:false

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

  let pp_debug out {name; ty; id} =
    fprintf out "%s[%d]:%a" name id (pp_type ~inside:false) ty
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
      fprintf fmt "λ%a %a" ID.pp id
        (pp_wrap inside (pp_term_ true)) t
    | Mu (id,t) ->
      fprintf fmt "@<1>µ%a %a" ID.pp id
        (pp_wrap inside (pp_term_ true)) t
  in
  pp_term_ false fmt term

let pp_ntterm fmt term =
  let rec pp_term_ inside fmt t = match t.expr with
    | Const id
    | Var id ->
      fprintf fmt "%s" (ID.name id)
      (* fprintf fmt "%a" ID.pp id *)
    | App (s,t) when inside ->
      fprintf fmt "(%a " (pp_term_ true) s;
      fprintf fmt "%a)" (pp_term_ true) t;
    | App (s,t) (* not inside *) ->
      fprintf fmt "%a " (pp_term_ true) s;
      fprintf fmt "%a" (pp_term_ true) t;
    | Abs (id,t) when inside ->
      fprintf fmt "(λ%a %a)" ID.pp id
        (pp_term_ true) t
    | Abs (id,t) (* not inside *) ->
      fprintf fmt "λ%a %a" ID.pp id
        (pp_term_ true) t
    | Mu (id,t) ->
      fprintf fmt "@<1>µ%a %a" ID.pp id
        (pp_term_ true) t
  in
  pp_term_ false fmt term


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
let pp_eval_mode fmt = function
  | SNF -> fprintf fmt "SNF"
  | WHNF -> fprintf fmt "WHNF"

(* Strong Normal Form *)
let dreduce debug t =
  let rec aux mode s t =
    if debug then printf "@<1>reduce: %a -- %a@," pp_term t pp_eval_mode mode else ();
    match t.expr with
    | Const _ -> t
    | Var _ -> subst s t
    | App (f', arg) ->
      let f = aux WHNF s f' in
      begin match f.expr, mode with
        | Abs (v, body), _ ->
          let arg = aux mode s arg in
          aux mode (IDMap.add v arg s) body
        | _, WHNF ->
          let arg = subst s arg in
          app f arg
        | _, SNF ->
          let arg = aux SNF s arg in
          let g = aux SNF s f in
          app g arg
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

let reduce = dreduce false

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

(* TLA encodings *)

module TLA = struct
  type quantifier = Forall | Exists

  let t_next = Tt --> Tt
  let t_rho = t_next --> (Tt --> Ti)
  let c_enabled = const (ID.make "EN" ((Tt --> Ti) --> Ti))

  (* quantifier represenatation: a quantifier takes the domain expression and
     the abstraction over the expression to return an expression *)
  let t_cquantifier  = (Ti --> t_rho) --> t_rho
  let t_vquantifier  = ((Tt --> Ti) --> t_rho) --> t_rho
  let t_cbquantifier = t_rho --> ((Ti --> t_rho) --> t_rho)
  let t_vbquantifier = t_rho --> (((Tt --> Ti) --> t_rho) --> t_rho)

  let c_forall_c = const (ID.make "∀"  t_cquantifier )
  let c_exists_c = const (ID.make "∃"  t_cquantifier )
  let c_forall_v = const (ID.make "∀∀" t_vquantifier )
  let c_exists_v = const (ID.make "∃∃" t_vquantifier )

  let c_bforall_c = const (ID.make "B∀"  t_cbquantifier )
  let c_bexists_c = const (ID.make "B∃"  t_cbquantifier )
  let c_bforall_v = const (ID.make "B∀∀" t_vbquantifier )
  let c_bexists_v = const (ID.make "B∃∃" t_vbquantifier )

  let is_trho = function
    | Arr (Arr (Tt, Tt), Arr ( Tt, Ti)) -> true
    | _ -> false

  let cid name arity =
    let rec tp acc = function
      | 0 -> acc
      | n when n > 0 ->
        tp (Ti --> acc) (n-1)
      | _ -> failwith "Arity must >= 0."
    in
    (ID.make name (tp Ti arity))


  let op_arity expr =
    let rec cid_arity_ n = function
      | t when is_trho t -> n
      | Arr (t, x) when is_trho t -> cid_arity_ (1+n) x
      | _ ->
        let msg = asprintf "%a is not an operator!" pp_term expr in
        failwith msg
    in cid_arity_ 0 expr.ty

  let c_arity ty =
    let rec cid_arity_ n = function
      | Ti -> n
      | Arr (Ti, x) -> cid_arity_ (1+n) x
      | _ ->
        let msg = asprintf "%a is not a constant type!"
            (pp_type ~inside:false) ty in
        failwith msg
    in cid_arity_ 0 ty


  let rec is_const_t = function
    | Ti -> true
    | Arr (Ti, x) -> is_const_t x
    | _ -> false

  let vid name = (ID.make name (Tt --> Ti))

  let c_op = function
    | c when ID.ty c |> is_const_t ->
      let rec mk_arg_ids acc = function
      | 0 ->
        acc
      | n when n > 0 ->
        let id = ID.make (Format.asprintf "arg%d" n) t_rho  in
        mk_arg_ids (id::acc) (n-1)
      | _  ->  failwith "A constant operator is of type Tnext^n --> Tnext."
      in
      (* create ids and vars for time *)
      let nid = (ID.make "n" (Tt --> Tt) ) in
      let tid = (ID.make "t" Tt) in
      let next = var nid in
      let time = var tid in
      (* create ids *)
      let arg_ids = mk_arg_ids [] (c_arity (ID.ty c)) in
      (* propagate next and time to the arguments *)
      let acc_ops =
        List.map (fun id -> (app (app (var id) next) time)) arg_ids in
      (* create inner term *)
      let s = app_l (var c) acc_ops in
      let inner = abs nid (abs tid s) in
      (* abstract over id for each argument *)
      let r = List.rev arg_ids |> List.fold_left
                (fun exp id -> abs id exp) inner
      in r
    | _ -> failwith "A constant operator is of type Tnext^n --> Tnext."

  let v_op id =
    match ID.ty id with
    | Arr (Tt, Ti) ->
      let nid = (ID.make "n" t_next ) in
      let s = var id in
      abs nid s
    | _  ->  failwith "A variable operator is of type Tt-->Ti."
(*
  let fp_op id =
    try ID.ty id with
*)
  let apply op args =
    match (op_arity op, List.length args) with
    | (n, m) when n = m ->
      app_l op args
    | _ -> failwith "Tried to apply operator of wrong arity!"

  let prime expr =
    match op_arity expr with
    | 0 ->
      (* prepare outer binders for enabled *)
      let nid = (ID.make "n" (Tt --> Tt) ) in
      let tid = (ID.make "t" Tt) in
      let next = var nid in
      let t = var tid in
      (* create t' as next of t *)
      let t_prime = app next t in
      (* abstract over next and time and push the modified time inside *)
      abs_l [nid; tid] (app_l expr [next; t_prime])
    | _ -> failwith "Can apply enabled only to expressions."

  let enabled expr =
    match op_arity expr with
    | 0 ->
      (* create id and var for the new state *)
      let en_id = ID.make "$en" Tt in
      let v = var en_id in
      (* create a new next state relation projecting to v *)
      let next = abs (ID.make "dummy" Tt) v in
      (* prepare outer binders for enabled *)
      let nid = (ID.make "n" (Tt --> Tt) ) in
      let tid = (ID.make "t" Tt) in
      let t = var tid in
      (* evaluate expr with the new next and current time. *)
      let enabled_term = app_l expr [next; t] in
      (* bind the new state en_id and wrap the term into the enabled constant *)
      let enabled = app c_enabled (abs en_id enabled_term) in
      (* abstract over next and t *)
      let term = abs_l [nid; tid] enabled in
      term
    | _ -> failwith "Can apply enabled only to expressions."


  let constant_quantifier q x ?domain:(domain=None) expr =
    let op = match q with
      | Forall -> c_forall_c
      | Exists -> c_exists_c
    in
    match domain, ID.ty x with
    | Some d, Ti ->
      app_l op [d; abs x expr]
    | None, Ti ->
      app op (abs x expr)
    | _, _ ->
      failwith "Must quantify over a (temporal) constant of type Ti."

  let variable_quantifier q x ?domain:(domain=None) expr =
    let op = match q with
      | Forall -> c_forall_v
      | Exists -> c_exists_v
    in
    match domain, ID.ty x with
    | Some d, Arr (Tt, Ti) ->
      app_l op [d; abs x expr]
    | None, Arr (Tt, Ti) ->
      app op (abs x expr)
    | _ ->
      failwith "Must quantify over a (temporal) variable of type Tt -> Ti."

end


module TT = struct
  let dif_id  = TLA.cid "[#]" 2
  let plus_id = TLA.cid "[+]" 2
  let zero_id = TLA.cid "[0]" 0
  let one_id  = TLA.cid "[1]" 0

  let zero = TLA.c_op zero_id
  let one  = TLA.c_op one_id
  let plus = TLA.c_op plus_id
  let dif  = TLA.c_op dif_id

  let xid = TLA.vid "x"
  let x = TLA.v_op xid

  let exp1 = TLA.apply plus [one; one] |> reduce
  let x_prime = TLA.prime x
  let exp2 = TLA.apply dif [x; x_prime]
  let exp3 = TLA.enabled exp2
  let exp4 = TLA.variable_quantifier TLA.Forall xid exp2
  let exp5 = TLA.apply dif [exp4; exp4] |> reduce
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
