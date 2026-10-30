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
callee is found, it is `first` over all of them. So it takes the step `first` takes, or fails
where `first` fails, but for a tag that names the wrong callee (then the build fails: the proof
is still checked).

    first_callee
      | "Warn" => (wp_apply hWarn lg _ _ $$ []; …)
      | "zap.String" => (wp_apply hZString as %_ -)
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
/-- The callee `e` names: the first `FuncResolve f _` or `MethodResolve _ m` in it, or the first
function or method it has resolved (`functions f _`, `methods _ m _`). -/
meta def resolveName? (e : Lean.Expr) : Option String := do
  let r ← e.find? fun x =>
    (x.isAppOfArity ``Perennial.GoInstruction.FuncResolve 2).or <|
      (x.isAppOfArity ``Perennial.GoInstruction.MethodResolve 2).or <|
      (isTableApp x "functions" 2).or (isTableApp x "methods" 3)
  if r.isAppOfArity ``Perennial.GoInstruction.FuncResolve 2 then goStringName? (r.getArg! 0)
  else if r.isAppOfArity ``Perennial.GoInstruction.MethodResolve 2 then goStringName? (r.getArg! 1)
  else if isTableApp r "functions" 2 then goStringName? (r.getArg! (r.getAppNumArgs - 2))
  else goStringName? (r.getArg! (r.getAppNumArgs - 2))

open Lean Elab Tactic Meta in
/-- The callee of the next call: the function or method the WP goal's next redex calls, if that
redex is a call (`f a` with `f` a resolved, or resolving, function or method). -/
meta def nextCallee? : TacticM (Option String) := withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOfArity ``Iris.ProofMode.Entails' 4 do return none
  let some wp ← Perennial.parseGooseWp? t.appArg! | return none
  let some (_, r) := (← Perennial.allEctx wp.e).getLast? | return none
  let r ← whnfR r
  let_expr Perennial.Expr.App _ f _ := r | return none
  return resolveName? f

/-- Whether the tag `t` names the callee `c`: `c` itself, or, for a tag with a package
(`"zap.String"`), its last components (a method's tag, `"String"`, is no function's). The primes
goose adds to a name Lean has taken are ignored (`"zap.Bool"` names `go_uber_org.zap.Bool'`). -/
meta def tagMatches (c t : String) : Bool :=
  let c := String.ofList (c.toList.reverse.dropWhile (· == '\'')).reverse
  (c == t).or ((t.contains '.').and (c.endsWith ("." ++ t)))

syntax firstCalleeAlt := (str " => ")? tacticSeq

/-- `first` over the alternatives, but those tagged with a callee other than the next call's
(module docstring). -/
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
    | none => alts
  let seqs : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := kept.map fun (p : Option String × Syntax) => ⟨p.2⟩
  evalTactic (← `(tactic| first $[| $seqs]*))

end FirstCallee
end EtcdGrove
end Perennial
