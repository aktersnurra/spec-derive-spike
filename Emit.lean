import Lean
import SpecDerive
import RejectCases

/-!
# Emit: print Lean definitions from a tiny subset as plain OCaml

`lake exe emit gen <outdir>` loads the compiled spec environment, takes the *elaborated*
definitions (the same terms the theorems are about) and prints them as OCaml source.
It is ordinary text generation: Lean `Expr` → a small OCaml AST (`OExpr`) → string.

## Supported subset (anything else is rejected with an error naming the definition)

* Types: `Int` (→ `int`), `Bool` (→ `bool`), `List T` (→ `T list`), `Option T`
  (→ `T option`; constructors only, no `Option` patterns), and monomorphic
  `structure`s declared in the example's namespace (→ OCaml records).
* Definitions: plain, safe, monomorphic `def`s in the example's namespace, fully applied.
  Recursion must be structural and non-mutual (→ `let rec`). No `partial`, `unsafe`,
  well-founded recursion, `implemented_by`, `@[extern]`, lambdas or higher-order code.
* Terms: variables, `let`, Int literals that fit in an OCaml int, `+ - *` and unary `-` on
  `Int`, `==`/`!=` on `Int`/`Bool`, `&&`, `||`, `!`, `true`, `false`, `[]`, `::`,
  `none`, `some`, structure constructors and field projections, `if c then a else b` where `c` is a `Bool`
  or a proposition built from `= ≠ < ≤ > ≥` on `Int`, `= ≠` on `Bool`, `¬ ∧ ∨ True False`,
  and `match` on the above with constructor / variable / wildcard patterns.
* Every operator instance must be definitionally equal to the standard one, so `+` really
  is `Int.add`. `/` and `%` are excluded (Lean `Int` division is Euclidean, OCaml's
  truncates); `Nat` is excluded (truncated subtraction, unbounded).

The generator does not check integer overflow. It counts Int arithmetic sites per function
and prints them in the header; each must be covered by a `Fits` theorem in the spec.
-/

open Lean Meta

namespace Emit

/-! ## OCaml AST and printer -/

inductive OPat where
  | var (n : String)
  | wild
  | nil
  | cons (h t : OPat)
  | bool (b : Bool)
  | record (fields : List (String × OPat))
  | tuple (ps : List OPat)
  deriving Inhabited

inductive OExpr where
  | var (n : String)
  | int (v : Int)
  | bool (b : Bool)
  | app (f : String) (args : List OExpr)
  | binop (op : String) (a b : OExpr)
  | neg (a : OExpr)
  | not (a : OExpr)
  | ite (c t e : OExpr)
  | mtch (scruts : List OExpr) (alts : List (OPat × OExpr))
  | letE (n : String) (v b : OExpr)
  | field (e : OExpr) (f : String)
  | record (fields : List (String × OExpr))
  | nil
  | cons (h t : OExpr)
  | none
  | some (a : OExpr)
  deriving Inhabited

def opPrec : String → Nat
  | "||" => 1
  | "&&" => 2
  | "+" | "-" => 5
  | "*" => 6
  | _ => 3 -- comparisons

/-- Precedence: 10 atom, 9 field, 8 application, 7 unary minus, 6..1 binary, 0 open-ended. -/
def OExpr.prec : OExpr → Nat
  | .var _ | .bool _ | .record _ | .nil | .none => 10
  | .int v => if v < 0 then 7 else 10
  | .field .. => 9
  | .app _ [] => 10
  | .app .. | .not _ | .some _ => 8
  | .neg _ => 7
  | .binop op .. => opPrec op
  | .cons .. => 4
  | .ite .. | .mtch .. | .letE .. => 0

def indent (n : Nat) : String := "".pushn ' ' n

partial def ppPat : OPat → String
  | .var n => n
  | .wild => "_"
  | .nil => "[]"
  | .bool b => toString b
  | .cons h .nil => "[" ++ ppPat h ++ "]"
  | .cons h t =>
    let hs := match h with | .cons .. | .tuple _ => "(" ++ ppPat h ++ ")" | _ => ppPat h
    hs ++ " :: " ++ ppPat t
  | .record fs => "{ " ++ "; ".intercalate (fs.map fun (n, p) => n ++ " = " ++ ppPat p) ++ " }"
  | .tuple ps => ", ".intercalate (ps.map ppPat)

mutual
/-- Print `e` at indentation `ind`, parenthesizing if its precedence is below `min`. -/
partial def pp (ind min : Nat) (e : OExpr) : String :=
  let s := ppRaw ind e
  if e.prec < min then "(" ++ s ++ ")" else s

partial def ppRaw (ind : Nat) : OExpr → String
  | .var n => n
  | .int v => toString v
  | .bool b => toString b
  | .nil => "[]"
  | .none => "None"
  | .some a => "Some " ++ pp ind 9 a
  | .app f [] => f
  | .app f args => f ++ " " ++ " ".intercalate (args.map (pp ind 9))
  | .not a => "not " ++ pp ind 9 a
  | .neg a => "- " ++ pp ind 8 a
  | .field a f => pp ind 9 a ++ "." ++ f
  | .record fs => "{ " ++ "; ".intercalate (fs.map fun (n, v) => n ++ " = " ++ pp ind 1 v) ++ " }"
  | .cons h t => pp ind 5 h ++ " :: " ++ pp ind 4 t
  | .binop op a b =>
    let p := opPrec op
    let (lm, rm) :=
      if op == "&&" || op == "||" then (p + 1, p)
      else if p == 3 then (p + 1, p + 1)
      else (p, p + 1)
    pp ind lm a ++ " " ++ op ++ " " ++ pp ind rm b
  | .ite c t e =>
    let elseBranch := match e with
      | .ite .. => " " ++ ppRaw ind e
      | _ => "\n" ++ indent (ind + 2) ++ pp (ind + 2) 0 e
    "if " ++ pp ind 1 c ++ " then\n" ++ indent (ind + 2) ++ pp (ind + 2) 1 t ++ "\n" ++
      indent ind ++ "else" ++ elseBranch
  | .letE n v b =>
    "let " ++ n ++ " = " ++ pp (ind + 2) 1 v ++ " in\n" ++ indent ind ++ pp ind 0 b
  | .mtch scruts alts =>
    let n := alts.length
    let alt (i : Nat) (pb : OPat × OExpr) :=
      let m := if i + 1 == n then 0 else 1
      let body :=
        if pb.2.prec > 0 then " " ++ pp (ind + 4) m pb.2
        else "\n" ++ indent (ind + 4) ++ pp (ind + 4) m pb.2
      "\n" ++ indent ind ++ "| " ++ ppPat pb.1 ++ " ->" ++ body
    "match " ++ ", ".intercalate (scruts.map (pp ind 1)) ++ " with" ++
      String.join (alts.mapIdx alt)
end

/-! ## Names -/

def ocamlReserved : List String :=
  ["and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done", "downto",
   "else", "end", "exception", "external", "false", "for", "fun", "function", "functor",
   "if", "in", "include", "inherit", "initializer", "land", "lazy", "let", "lor", "lsl",
   "lsr", "lxor", "match", "method", "mod", "module", "mutable", "new", "nonrec", "object",
   "of", "open", "or", "private", "rec", "sig", "struct", "then", "to", "true", "try",
   "type", "val", "virtual", "when", "while", "with", "not"]

/-- `checkInvariant` → `check_invariant`, `Entry` → `entry`. -/
def snake (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c.isUpper then (if acc.isEmpty then acc else acc.push '_').push c.toLower
    else acc.push c

/-- A valid lowercase OCaml identifier derived from a Lean name component. -/
def sanitize (s : String) : String :=
  let s := snake s
  let s := s.foldl (init := "") fun acc c =>
    if c.isAlphanum || c == '_' || c == '\'' then
      if c.toNat < 128 then acc.push c else acc
    else acc.push '_'
  let s := if s.isEmpty || s.front.isDigit || s.front == '\'' then "v" ++ s else s
  if ocamlReserved.contains s then s ++ "_" else s

def lastComponent (n : Name) : String :=
  match n.eraseMacroScopes with
  | .str _ s => s
  | _ => "v"

def ocamlName (n : Name) : String := sanitize (lastComponent n)

/-! ## Translation -/

structure St where
  ns : Name
  names : Std.HashMap FVarId String := {}
  used : Std.HashSet String := {}
  deps : Array Name := #[]
  sites : Nat := 0
  /-- Structures in dependency order, with their OCaml declarations. -/
  types : Array (Name × String) := #[]
  typesInProgress : Array Name := #[]

abbrev TrM := StateRefT St MetaM

def inNs (c : Name) : TrM Bool := return c.getPrefix == (← get).ns

def isUserStruct (c : Name) : TrM Bool := do
  return (← inNs c) && isStructure (← getEnv) c

def bindFVar (x : FVarId) : TrM String := do
  let base := sanitize (lastComponent (← x.getUserName))
  let st ← get
  let mut n := base
  let mut i := 1
  while st.used.contains n do
    n := s!"{base}_{i}"
    i := i + 1
  modify fun s => { s with used := s.used.insert n, names := s.names.insert x n }
  return n

/-- Name for a binder; `_`-prefixed when unused so OCaml does not warn. -/
def bindBinder (x : Expr) (body : Expr) : TrM String := do
  let n ← bindFVar x.fvarId!
  return if body.containsFVar x.fvarId! then n else "_" ++ n

def requireConst (ty : Expr) (allowed : List Name) (what : String) : TrM Name := do
  let ty ← instantiateMVars ty
  match ty.consumeMData with
  | .const c [] => if allowed.contains c then return c else throwError "{what} at type {ty} is outside the subset"
  | _ => throwError "{what} at type {ty} is outside the subset"

/-- The instance must be definitionally equal to the one Lean synthesizes. -/
def checkStdInst (inst : Expr) : TrM Unit := do
  let ty ← inferType inst
  let some std ← synthInstance? ty | throwError "no standard instance for {ty}"
  unless ← isDefEq inst std do throwError "non-standard instance {inst} : {ty}"

mutual
partial def trType (t : Expr) : TrM String := do
  let t := (← instantiateMVars t).consumeMData.headBeta
  match t.getAppFn, t.getAppArgs with
  | .const ``Int [], #[] => return "int"
  | .const ``Bool [], #[] => return "bool"
  | .const ``List _, #[a] => return s!"{← trType a} list"
  | .const ``Option _, #[a] => return s!"{← trType a} option"
  | .const c [], #[] =>
    if ← isUserStruct c then
      registerStruct c
      return ocamlName c
    throwError "type {t} is outside the subset"
  | _, _ => throwError "type {t} is outside the subset"

partial def registerStruct (c : Name) : TrM Unit := do
  let st ← get
  if st.types.any (·.1 == c) then return
  if st.typesInProgress.contains c then throwError "recursive structure {c} is outside the subset"
  modify fun s => { s with typesInProgress := s.typesInProgress.push c }
  let env ← getEnv
  let ctor := getStructureCtor env c
  unless ctor.numParams == 0 do throwError "parameterized structure {c} is outside the subset"
  let fields ← forallTelescope ctor.type fun xs _ => xs.toList.mapM fun x => do
    return s!"{ocamlName (← x.fvarId!.getUserName)} : {← trType (← inferType x)}"
  let decl := s!"type {ocamlName c} = \{ {"; ".intercalate fields} }"
  modify fun s => { s with types := s.types.push (c, decl) }
end

def fieldName (s : Name) (i : Nat) : TrM String := do
  let fields := getStructureFields (← getEnv) s
  let some f := fields[i]? | throwError "bad projection index {i} for {s}"
  return ocamlName f

mutual
partial def trExpr (e : Expr) : TrM OExpr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  match e with
  | .fvar id =>
    let some n := (← get).names[id]? | throwError "unbound variable {e}"
    return .var n
  | .letE n ty v b _ =>
    discard <| trType ty
    let v' ← trExpr v
    withLetDecl n ty v fun x => do
      let b := b.instantiate1 x
      let n ← bindBinder x b
      return .letE n v' (← trExpr b)
  | .proj s i x =>
    unless ← isUserStruct s do throwError "projection from {s} is outside the subset"
    return .field (← trExpr x) (← fieldName s i)
  | .app .. | .const .. => trApp e
  | _ => throwError "expression {e} is outside the subset (lambdas, literals of raw Nat, etc.)"

partial def arith (op : String) (args : Array Expr) : TrM OExpr := do
  for i in [0:3] do discard <| requireConst args[i]! [``Int] s!"`{op}`"
  checkStdInst args[3]!
  modify fun s => { s with sites := s.sites + 1 }
  return .binop op (← trExpr args[4]!) (← trExpr args[5]!)

partial def trApp (e : Expr) : TrM OExpr := do
  if let some m ← matchMatcherApp? e then return ← trMatch m
  let .const c _ := e.getAppFn
    | throwError "application of a non-constant {e} (higher-order code) is outside the subset"
  let args := e.getAppArgs
  match c, args.size with
  | ``List.nil, 1 => return .nil
  | ``List.cons, 3 => return .cons (← trExpr args[1]!) (← trExpr args[2]!)
  | ``Option.none, 1 => return .none
  | ``Option.some, 2 => return .some (← trExpr args[1]!)
  | ``Bool.true, 0 => return .bool true
  | ``Bool.false, 0 => return .bool false
  | ``OfNat.ofNat, 3 =>
    discard <| requireConst args[0]! [``Int] "numeric literal"
    checkStdInst args[2]!
    let .lit (.natVal n) := args[1]!.consumeMData | throwError "non-literal OfNat {e}"
    unless n ≤ 4611686018427387903 do throwError "literal {n} does not fit in an OCaml int"
    return .int n
  | ``HAdd.hAdd, 6 => arith "+" args
  | ``HSub.hSub, 6 => arith "-" args
  | ``HMul.hMul, 6 => arith "*" args
  | ``Neg.neg, 3 =>
    discard <| requireConst args[0]! [``Int] "negation"
    checkStdInst args[1]!
    match ← trExpr args[2]! with
    | .int v => return .int (-v)
    | a =>
      modify fun s => { s with sites := s.sites + 1 }
      return .neg a
  | ``BEq.beq, 4 | ``bne, 4 =>
    discard <| requireConst args[0]! [``Int, ``Bool] "`==`"
    checkStdInst args[1]!
    return .binop (if c == ``BEq.beq then "=" else "<>") (← trExpr args[2]!) (← trExpr args[3]!)
  | ``and, 2 => return .binop "&&" (← trExpr args[0]!) (← trExpr args[1]!)
  | ``or, 2 => return .binop "||" (← trExpr args[0]!) (← trExpr args[1]!)
  | ``not, 1 => return .not (← trExpr args[0]!)
  | ``decide, 2 => trProp args[0]!
  | ``ite, 5 => return .ite (← trProp args[1]!) (← trExpr args[3]!) (← trExpr args[4]!)
  | ``cond, 4 => return .ite (← trExpr args[1]!) (← trExpr args[2]!) (← trExpr args[3]!)
  | _, _ =>
    let env ← getEnv
    if let some info ← getProjectionFnInfo? c then
      let s := c.getPrefix
      if (← isUserStruct s) && args.size == info.numParams + 1 then
        return .field (← trExpr args[info.numParams]!) (← fieldName s info.i)
    if let some (.ctorInfo ci) := env.find? c then
      if (← isUserStruct ci.induct) && args.size == ci.numParams + ci.numFields then
        registerStruct ci.induct
        let fields := getStructureFields env ci.induct
        let vals ← (args.extract ci.numParams args.size).toList.mapM trExpr
        return .record (fields.toList.map ocamlName |>.zip vals)
    if (← inNs c) && (env.find? c).any (·.isDefinition) then
      let arity ← forallTelescope (← inferType (mkConst c)) fun xs _ => pure xs.size
      unless args.size == arity do throwError "partial application of {c} is outside the subset"
      modify fun s => { s with deps := if s.deps.contains c then s.deps else s.deps.push c }
      return .app (ocamlName c) (← args.toList.mapM trExpr)
    throwError "constant {c} (with {args.size} args) is outside the subset"

partial def trProp (p : Expr) : TrM OExpr := do
  let p := (← instantiateMVars p).consumeMData
  let args := p.getAppArgs
  let cmp (op : String) : TrM OExpr := do
    discard <| requireConst args[0]! [``Int] s!"`{op}`"
    checkStdInst args[1]!
    return .binop op (← trExpr args[2]!) (← trExpr args[3]!)
  match p.getAppFn.constName?, args.size with
  | some ``Eq, 3 | some ``Ne, 3 =>
    discard <| requireConst args[0]! [``Int, ``Bool] "equality"
    let pos := p.isAppOf ``Eq
    match args[2]!.consumeMData with
    | .const ``Bool.true [] =>
      let a ← trExpr args[1]!
      return if pos then a else .not a
    | _ => return .binop (if pos then "=" else "<>") (← trExpr args[1]!) (← trExpr args[2]!)
  | some ``LT.lt, 4 => cmp "<"
  | some ``LE.le, 4 => cmp "<="
  | some ``GT.gt, 4 => cmp ">"
  | some ``GE.ge, 4 => cmp ">="
  | some ``Not, 1 => return .not (← trProp args[0]!)
  | some ``And, 2 => return .binop "&&" (← trProp args[0]!) (← trProp args[1]!)
  | some ``Or, 2 => return .binop "||" (← trProp args[0]!) (← trProp args[1]!)
  | some ``True, 0 => return .bool true
  | some ``False, 0 => return .bool false
  | _, _ => throwError "proposition {p} is outside the subset"

partial def trPat (body : Expr) (p : Expr) : TrM OPat := do
  let p := p.consumeMData
  if p.isFVar then
    if body.containsFVar p.fvarId! then return .var (← bindFVar p.fvarId!) else return .wild
  let args := p.getAppArgs
  match p.getAppFn.constName?, args.size with
  | some ``List.nil, 1 => return .nil
  | some ``List.cons, 3 => return .cons (← trPat body args[1]!) (← trPat body args[2]!)
  | some ``Bool.true, 0 => return .bool true
  | some ``Bool.false, 0 => return .bool false
  | some c, _ =>
    if let some (.ctorInfo ci) := (← getEnv).find? c then
      if (← isUserStruct ci.induct) && args.size == ci.numParams + ci.numFields then
        let fields := getStructureFields (← getEnv) ci.induct
        let ps ← (args.extract ci.numParams args.size).toList.mapM (trPat body)
        return .record (fields.toList.map ocamlName |>.zip ps)
    throwError "pattern {p} is outside the subset"
  | none, _ => throwError "pattern {p} is outside the subset"

partial def trMatch (m : MatcherApp) : TrM OExpr := do
  unless m.remaining.isEmpty do throwError "match producing a function is outside the subset"
  if m.discrInfos.any (·.hName?.isSome) then throwError "`match h : ...` is outside the subset"
  let scruts ← m.discrs.toList.mapM trExpr
  let mType ← inferType (mkAppN (mkConst m.matcherName m.matcherLevels.toList) m.params)
  forallBoundedTelescope mType (some (1 + m.discrs.size + m.alts.size)) fun xs _ => do
    let motive := xs[0]!
    let mut alts := #[]
    for i in [0:m.alts.size] do
      let altType ← inferType xs[1 + m.discrs.size + i]!
      let alt ← forallTelescope altType fun vars res => do
        unless res.getAppFn == motive && res.getAppNumArgs == m.discrs.size do
          throwError "unexpected matcher alternative type {altType}"
        let body := (m.alts[i]!.beta vars).headBeta
        let pats ← res.getAppArgs.toList.mapM (trPat body)
        let pat := match pats with | [p] => p | ps => .tuple ps
        return (pat, ← trExpr body)
      alts := alts.push alt
    return .mtch scruts alts.toList
end

/-! ## Definitions -/

structure FnOut where
  lean : Name
  name : String
  isRec : Bool
  params : List (String × String)
  ret : String
  body : OExpr
  deps : Array Name
  sites : Nat

def recursionConsts : List String := ["brecOn", "rec", "fix", "fixF", "WellFounded"]

def trDef (c : Name) : TrM FnOut := do
  let env ← getEnv
  let some ci := env.find? c | throwError "unknown constant {c}"
  let .defnInfo di := ci
    | throwError "{c} is not a plain definition (opaque/partial/axiom/theorem are outside the subset)"
  unless di.levelParams.isEmpty do throwError "{c} is universe polymorphic"
  unless di.safety == .safe do throwError "{c} is unsafe or partial"
  if (Compiler.getImplementedBy? env c).isSome then throwError "{c} uses implemented_by"
  if isExtern env c then throwError "{c} is @[extern]"
  if (Elab.WF.eqnInfoExt.find? env c).isSome then
    throwError "{c} uses well-founded recursion; only structural recursion is supported"
  let structInfo := Elab.Structural.eqnInfoExt.find? env c
  if let some info := structInfo then
    unless info.declNames.size == 1 do throwError "{c} is mutually recursive"
  else if di.value.getUsedConstants.any (fun n => recursionConsts.any (lastComponent n == ·)) then
    throwError "{c} uses a recursion scheme other than structural recursion"
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | throwError "no unfold equation for {c}"
  let eqTy ← inferType (mkConst eqn)
  modify fun s => { s with names := {}, deps := #[], sites := 0 }
  forallTelescope eqTy fun xs eqBody => do
    let some (_, lhs, rhs) := eqBody.eq? | throwError "unexpected equation for {c}"
    unless lhs.isAppOf c && lhs.getAppArgs == xs do
      throwError "{c}: point-free or higher-order definition is outside the subset"
    let ret ← trType (← inferType lhs)
    let params ← xs.toList.mapM fun x => do
      let ty ← trType (← inferType x)
      return (← bindBinder x rhs, ty)
    let body ← trExpr rhs
    let st ← get
    return { lean := c, name := ocamlName c, isRec := (rhs.find? (·.isConstOf c)).isSome,
             params, ret, body, deps := st.deps.filter (· != c), sites := st.sites }

/-- The fixed interface every example exports. -/
def interface : List String := ["reference", "plan", "checkInvariant", "run"]

/-- An example: OCaml file stem, Lean namespace, and extra exported operations
(e.g. invariant-preserving `push`) beyond the fixed interface. -/
structure Example where
  stem : String
  ns : Name
  ops : List String := []

/-- Translate the interface and its dependencies, dependencies first. -/
partial def trExample (ns : Name) (exports : List String) : TrM (Array FnOut) := do
  let used := (← getEnv).constants.fold (init := ocamlReserved) fun acc n _ =>
    if n.getPrefix == ns then ocamlName n :: acc else acc
  let rec visit (stack : List Name) (out : Array FnOut) (c : Name) : TrM (Array FnOut) := do
    if out.any (·.lean == c) then return out
    if stack.contains c then throwError "mutual recursion through {c} is outside the subset"
    modify fun s => { s with used := Std.HashSet.ofList used }
    let f ← try trDef c catch e => throwError "in {c}: {e.toMessageData}"
    let mut out := out
    for d in f.deps do out ← visit (c :: stack) out d
    if out.any (·.name == f.name) then throwError "OCaml name clash: {f.name}"
    return out.push f
  let mut out := #[]
  for r in exports do out ← visit [] out (ns ++ Name.mkSimple r)
  return out

/-! ## Files -/

def commentSafe (s : String) : String := (s.replace "(*" "( *").replace "*)" "* )"

def header (ns : Name) (fns : Array FnOut) (types : Array Name) : MetaM String := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? (ns ++ `reference) | throwError "no module for {ns}"
  let modName := env.header.moduleNames[idx.toNat]!
  let defs := types.toList.map toString ++ fns.toList.map (toString ·.lean)
  let sites := fns.toList.filter (·.sites > 0) |>.map fun f => s!"{f.name}: {f.sites}"
  let sitesLine := if sites.isEmpty then "none" else ", ".intercalate sites
  return s!"(* GENERATED by Emit.lean (`lake exe emit gen gen`). DO NOT EDIT.
   Lean module: {modName}
   Lean definitions: {" ".intercalate defs}
   Int arithmetic sites (each must be covered by a Fits theorem in the spec): {sitesLine}
   Precondition: inputs satisfy the spec's `Bounded` predicate. *)
"

def ppFn (f : FnOut) (first : Bool) : String :=
  let kw := if first then (if f.isRec then "let rec" else "let") else "and"
  let ps := " ".intercalate (f.params.map fun (n, t) => s!"({n} : {t})")
  s!"{kw} {f.name} {ps} : {f.ret} =\n  {pp 2 0 f.body}\n"

def mliVal (f : FnOut) : MetaM String := do
  let doc := match ← findDocString? (← getEnv) f.lean with
    | some d => s!"(** {commentSafe d.trimAscii.toString} *)\n"
    | none => ""
  let tys := f.params.map (·.2) ++ [f.ret]
  return s!"{doc}val {f.name} : {" -> ".intercalate tys}\n"

/-- Returns the `.ml` and `.mli` contents for the example in namespace `ns`. -/
def emitExample (ex : Example) : MetaM (String × String) := do
  let ns := ex.ns
  let exports := interface ++ ex.ops
  let (fns, st) ← (trExample ns exports).run { ns }
  let hdr ← header ns fns (st.types.map (·.1))
  let types := "\n".intercalate (st.types.toList.map (·.2)) ++ "\n"
  let ml := hdr ++ "\n" ++ types ++ String.join (fns.toList.map fun f => "\n" ++ ppFn f true)
  let exported := fns.filter fun f => exports.any (ns ++ Name.mkSimple · == f.lean)
  let vals ← exported.toList.mapM mliVal
  let mli := hdr ++ "\n" ++ types ++ String.join (vals.map ("\n" ++ ·))
  return (ml, mli)

/-- Registered examples. -/
def examples : List Example :=
  [{ stem := "running_sum", ns := `RunningSum, ops := ["push"] },
   { stem := "sorted_lookup", ns := `SortedLookup }]

unsafe def runMeta (act : MetaM α) : IO α := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `SpecDerive }, { module := `RejectCases }] {}
    (loadExts := true)
  let ctx : Core.Context := { fileName := "<emit>", fileMap := default, maxHeartbeats := 0 }
  let (a, _) ← (act.run' {} {}).toIO ctx { env }
  return a

unsafe def genAll (outDir : System.FilePath) : IO Unit := do
  let files ← runMeta <| examples.mapM fun ex => do
    let (ml, mli) ← emitExample ex
    return [(s!"{ex.stem}_gen.ml", ml), (s!"{ex.stem}_gen.mli", mli)]
  IO.FS.createDirAll outDir
  for (name, contents) in files.flatten do
    IO.FS.writeFile (outDir / name) contents

/-- Expect the definition `c` (in its own namespace) to be rejected. -/
unsafe def expectReject (c : Name) : IO Bool := do
  runMeta do
    try
      discard <| (trDef c).run { ns := c.getPrefix }
      IO.eprintln s!"ACCEPTED (expected rejection): {c}"
      return false
    catch e =>
      IO.println s!"rejected {c}: {← e.toMessageData.toString}"
      return true

end Emit

unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["gen", dir] => Emit.genAll dir; return 0
    | "reject" :: names =>
      let oks ← names.mapM (Emit.expectReject ·.toName)
      return if oks.all id then 0 else 1
    | _ =>
      IO.eprintln "usage: emit gen <outdir> | emit reject <Lean.Name>..."
      return 2
  catch e =>
    IO.eprintln s!"emit: error: {e}"
    return 1
