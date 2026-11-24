/- `first_callee`: `first` whose alternatives may be tagged with the callee they are for, the
others skipped when the next redex calls another (2026-10-30, a build-speed helper).

The proofs' log and getter macros (`zap_log`, `dl_dropped`, ...) are `repeat' (first | wp_apply
spec₁ … | wp_apply spec₂ … | … | wp_auto)`: each step tries the alternatives in turn until one
applies, and a `wp_apply` whose spec does not fit the next call costs a tenth of a second or more
on a large function body (`wp_apply` runs `wp_pures` before giving up). Most of it is the last
round, where every alternative fails (the code after the log call is another call).

`first_callee` reads the callee of the next redex off the goal, if that redex is a call (as
`raft__Step/Dispatch.lean`'s `nextMethod?`): a method's name (`"Warn"`), or a function's (the
`GoString` constant it is resolved by, `go_uber_org.zap.String`, which the tag `"zap.String"`
names). It then runs `first` over the alternatives in their order, without those tagged with
another callee: each is a spec of another function, which cannot apply to this call. Where no
callee is found, it is `first` over all of them (the untagged first: below). So it takes the step
`first` takes, or fails where `first` fails, but for a tag that names the wrong callee (then the
build fails: the proof is still checked).

Two refinements (2026-11-18). A method's tag may name its receiver type, `"ID.String"` or
`"*ID.String"` (pointer receiver), so that the specs of several `String` methods are not all
tried on each `String` call. And where no callee is found (the next redex is not a call: an `if`,
a slice literal, a load), the untagged alternatives are tried first: a tagged one, a call's spec,
fails there (unless `wp_apply`'s own pure steps reach the call, which an untagged `wp_auto` then
takes instead, leaving the call to the next round), and each failure costs a `wp_apply`
(`streamReader.decodeLoop`'s `dl_dropped`: 32 such steps, each about 2.5s of failed specs).

    first_callee
      | "Warn" => (wp_apply hWarn lg _ _ $$ []; …)
      | "zap.String" => (wp_apply hZString as %_ -)
      | "ID.String" => (wp_apply hIDString as %_ -)
      | wp_auto -/
module

public import Perennial.Golang.Theory.ProofMode

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace FirstCallee

open Lean in
/-- The natural-number literals of `e`. -/
meta partial def natLits : Lean.Expr → List Nat
  | .lit (.natVal n) => [n]
  | .app f a => natLits f ++ natLits a
  | .mdata _ b => natLits b
  | _ => []

open Lean in
/-- The bytes of a byte-list literal `[71#8, 101#8, ...]` as characters (each byte's largest
literal: the other is the width `8`). -/
meta partial def byteChars (l : Lean.Expr) : List Char :=
  if l.isAppOfArity ``List.cons 3 then
    Char.ofNat ((natLits (l.getArg! 1)).foldl max 0) :: byteChars (l.getArg! 2)
  else []

open Lean in
/-- The name of a `GoString`: a byte-list literal's characters, else the name of the constant it
applies (a function's name, `go_uber_org.zap.String` applied to the instances). -/
meta def goStringName? (s : Lean.Expr) : Option String :=
  let s := s.consumeMData
  if s.isAppOfArity ``List.cons 3 then some (String.ofList (byteChars s))
  else s.getAppFn.constName?.map (·.toString)

open Lean in
/-- Whether `x` is an application of the function table `functions f ts` or the method table
`methods t m v` (the values `FuncResolve`, `MethodResolve` resolve to), at least `k` arguments. -/
meta def isTableApp (x : Lean.Expr) (tbl : String) (k : Nat) : Bool :=
  match x.getAppFn.constName? with
  | some n => (n.components.getLast?.map (·.toString) == some tbl).and (x.getAppNumArgs ≥ k)
  | none => false

open Lean in
/-- The name of a receiver type, as a tag writes it: the type's own name (`ID` for
`types.ID.ty`, the last component but goose's `ty`), with `*` before it for a pointer
(`go.PointerType types.ID.ty`: `*ID`); `none` for another type expression. -/
meta partial def recvName? (t : Lean.Expr) : Option String :=
  let t := t.consumeMData
  if (t.getAppFn.constName?.map (·.components.getLast?.map (·.toString))).join == some "PointerType"
      && t.getAppNumArgs ≥ 1 then
    (recvName? t.appArg!).map ("*" ++ ·)
  else
    match t.getAppFn.constName? with
    | some n =>
      let cs := n.components.map (·.toString)
      let cs := if cs.getLast? == some "ty" then cs.dropLast else cs
      cs.getLast?
    | none => none

/-- The callee of a call: a function's name (the `GoString` constant it is resolved by), or a
method's name with its receiver type's (`recvName?`), if known. -/
structure Callee where
  name : String
  recv : Option String := none
  isMethod : Bool := false

open Lean in
/-- The callee `e` names: the first `FuncResolve f _` or `MethodResolve t m` in it, or the first
function or method it has resolved (`functions f _`, `methods t m _`). -/
meta def resolveCallee? (e : Lean.Expr) : Option Callee := do
  let r ← e.find? fun x =>
    (x.isAppOfArity ``Perennial.GoInstruction.FuncResolve 2).or <|
      (x.isAppOfArity ``Perennial.GoInstruction.MethodResolve 2).or <|
      (isTableApp x "functions" 2).or (isTableApp x "methods" 3)
  if r.isAppOfArity ``Perennial.GoInstruction.FuncResolve 2 then
    return { name := ← goStringName? (r.getArg! 0) }
  else if r.isAppOfArity ``Perennial.GoInstruction.MethodResolve 2 then
    return { name := ← goStringName? (r.getArg! 1), recv := recvName? (r.getArg! 0), isMethod := true }
  else if isTableApp r "functions" 2 then
    return { name := ← goStringName? (r.getArg! (r.getAppNumArgs - 2)) }
  else
    return { name := ← goStringName? (r.getArg! (r.getAppNumArgs - 2)),
             recv := recvName? (r.getArg! (r.getAppNumArgs - 3)), isMethod := true }

open Lean Elab Tactic Meta in
/-- The callee of the next call: the function or method the WP goal's next redex calls, if that
redex is a call (`f a` with `f` a resolved, or resolving, function or method). -/
meta def nextCallee? : TacticM (Option Callee) := withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOfArity ``Iris.ProofMode.Entails' 4 do return none
  let some wp ← Perennial.parseGooseWp? t.appArg! | return none
  let some (_, r) := (← Perennial.allEctx wp.e).getLast? | return none
  let r ← whnfR r
  let_expr Perennial.Expr.App _ f _ := r | return none
  return resolveCallee? f

/-- Whether the tag `t` names the callee `c`. A function's tag is its name, or its last
components with its package (`"zap.String"`; a tag without a package, `"String"`, is no
function's). A method's tag is its name (`"String"`), or its name after its receiver type's
(`"ID.String"`, `"*ID.String"` for a pointer receiver: `recvName?`), which no other receiver
type's method matches. The primes goose adds to a name Lean has taken are ignored (`"zap.Bool"`
names `go_uber_org.zap.Bool''`). -/
meta def tagMatches (c : Callee) (t : String) : Bool :=
  let n := String.ofList (c.name.toList.reverse.dropWhile (· == '\'')).reverse
  if c.isMethod then
    (n == t).or <| match c.recv with
      | some r => t == r ++ "." ++ n
      | none => (t.endsWith ("." ++ n))
  else
    (n == t).or ((t.contains '.').and (n.endsWith ("." ++ t)))

syntax firstCalleeAlt := (str " => ")? tacticSeq

/-- `first` over the alternatives, but those tagged with a callee other than the next call's; the
untagged ones first if the next redex is no call (module docstring). -/
syntax (name := firstCallee) "first_callee " withPosition((ppDedent(ppLine) colGe "| " firstCalleeAlt)+) :
    tactic

open Lean Elab Tactic in
@[tactic firstCallee] meta def evalFirstCallee : Tactic := fun stx => do
  let alts : Array (Option String × Syntax) := stx[1].getArgs.map fun a =>
    let alt := a[1]
    let tag := if alt[0].isNone then none else alt[0][0].isStrLit?
    (tag, alt[1])
  let callee ← nextCallee?
  let kept := match callee with
    | some c => alts.filter fun (p : Option String × Syntax) => p.1.all (tagMatches c)
    | none => alts.filter (fun (p : Option String × Syntax) => p.1.isNone) ++
        alts.filter (fun (p : Option String × Syntax) => p.1.isSome)
  let seqs : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := kept.map fun (p : Option String × Syntax) => ⟨p.2⟩
  evalTactic (← `(tactic| first $[| $seqs]*))

end FirstCallee
end EtcdGrove
end Perennial
