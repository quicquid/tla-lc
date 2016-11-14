open Format

type tp = Ti | To | Arr of tp * tp

type id = Id of string * tp
type expr = Const of id | Var of id | App of expr * expr
          | Abs of id * expr

type single_sub = Mapsto of id * expr

let (-->) x y = Arr (x, y)

let (|->) x y = Mapsto (x, y)

let iname (Id (n, _)) = n
let itype (Id (_, t)) = t

let eid = function
  | Const i
  | Var i -> i
  | App (_, _)
  | Abs (_, _) -> failwith "App and abs don't have an id."

let rec etype = function
  | Const (Id (_, t)) -> t
  | Var (Id (_, t)) -> t
  | App (s,t) ->
    begin
      match (etype s), (etype t) with
      | Arr (x,y), z when x = z -> y
      | Arr (x,y), _ ->
        failwith "Types in app don't fit."
      | _, _ ->
        failwith "First type in app must be an arrow."
    end
  | Abs (Id (_,t0),t) ->
    Arr (t0, etype t)

let const s t = Const (Id (s, t))
let var s t = Var (Id (s, t))
let app s t =
  let r = App (s, t) in
  let _ = etype r in (* typecheck *)
  r

let abs v e =
  match v with
  | Var v ->
    Abs (v, e)
  | _ ->
    failwith "abstraction only over vars"


let rec free ?acc:(acc=[]) ?bound:(bound=[]) = function
  | Const _ -> acc
  | Var v ->
    if List.mem v bound then
      acc
    else
      v :: acc
  | App (s, t) ->
    free ~acc:(free ~acc ~bound t) ~bound s
  | Abs (x, t) ->
    free ~acc ~bound:(x::bound) t

let rename id (context : id list) =
  let check name context =
    List.for_all (function Id (x, _) -> x <> name) context
  in
  let rec rename_ n name context =
    let name' = asprintf "%s%d" name n in
    if check name' context then
      name'
    else
      rename_ (n+1) name context
  in
  if check (iname id) context then
    id
  else
    let name = rename_ 0 (iname id) context in
    Id (name, (itype id))

let range s = List.fold_left
    (fun x -> function Mapsto (v,e) -> List.append x (free e)) [] s

let rec subst s = function
  | Const id -> Const id
  | (Var id) as v ->
    begin
      try
        let Mapsto (_, r) =
          List.find (function | Mapsto (x, _) -> x = id) s
        in r
      with
        | Not_found -> v
    end
  | App (e, f) ->
    app (subst s e) (subst s f)
  | Abs (id, e) ->
    let id' = rename id (range s) in
    let s' = List.filter (function Mapsto (Id (name, _), _) -> name <> iname id') s in
    Abs (id', subst s' e)

let rec reduce t =
  match t with
  | Var id
  | Const id -> t
  | App (Abs( id, e), f) ->
    subst [id |-> f] e |> reduce
  | App (e, f) ->
    app (reduce e) (reduce f)
  | Abs (id, e) ->
    abs (Var id) (reduce e)


let pp_wrap conditon pp_fmt fmt x=
  if conditon then
    fprintf fmt "(%a)" pp_fmt x
  else
    fprintf fmt "%a" pp_fmt x

let pp_cond conditon pp_fmt fmt x =
  if conditon then
    fprintf fmt "%a" pp_fmt x
  else
    ()


let rec pp_type ?inside:(ins=false) fmt = function
  | Ti -> fprintf fmt "i"
  | To -> fprintf fmt "o"
  | Arr(t1, t2) ->
    fprintf fmt "%a>%a" (pp_wrap ins pp_type) t1 (pp_wrap ins pp_type) t2


let pp_term fmt term =
  let rec pp_term_ inside fmt = function
    | Var ((Id (name, t)) as id) ->
      fprintf fmt "%s" name;
      fprintf fmt ":%a" (pp_type ~inside:false) t;
    | Const ((Id (name, t)) as id) ->
      fprintf fmt "%s" name;
      fprintf fmt ":%a" (pp_type ~inside:false) t;
    | App (s,t) ->
      fprintf fmt "%a "
        (pp_wrap inside (pp_term_ true)) s;
      fprintf fmt "%a"
        (pp_wrap inside (pp_term_ true)) t
    | Abs (Id(name,ty),t) ->
      fprintf fmt "\\%s:%a %a" name
        (pp_type ~inside:false) ty
        (pp_term_ true) t
  in
  pp_term_ false fmt term

(* test terms *)
module T = struct
  let x = var "x" Ti
  let y = Var (Id ("y", Ti --> Ti))
  let z = Var (Id ("z", Ti))

  let e1 = Abs (Id ("x", Ti),z)
  let e2 = app (abs x (abs z x)) z
end
