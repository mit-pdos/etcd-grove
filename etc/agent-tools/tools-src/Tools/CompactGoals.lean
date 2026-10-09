/-
Compact goal printing for Perennial/Goose proofs (display only; no effect on proofs).

Importing this module turns on, in goals *and* error messages:

1. `goose.pp.goStrings` (default true): a literal list of printable bytes
   `[105#8, 116#8, 101#8, 109#8, 115#8]` is printed `go!"items"` (exact: it is
   the `go!` literal that elaborates to that list), e.g. struct fields
   `n.[node V, go!"items"]` and methods `methods (node.ty T).PointerType go!"get"`.
2. `goose.pp.lets` (default true): the GooseLang abbreviations `Let`, `Lam`, `Seq`
   (left unfolded by some tactics) are printed with the `let:`/`λ:`/`;;` notation.
3. `goose.pp.compactWP` (default true): in `WP e {{ Φ }}` only the next statements
   of `e` are printed and the rest of the program is `…`:
   - along the evaluation order, the first `goose.pp.compactWP.stmts` (default 4)
     statements (`let:`, `;;`, `;;;` nodes) are shown, then `…`;
   - a nested block (an `if:` branch, a function body, a loop body) shows its first
     `goose.pp.compactWP.inner` (default 1) statements, down to nesting depth
     `goose.pp.compactWP.depth` (default 2); deeper blocks are `…`.
   The statement that runs next is printed (its own nested lets count against the
   budget, so a deeply nested head can be cut after its first lets; the redex that
   runs first is always shown). A program printed on its own (as in `wp_apply`'s
   "cannot apply ... to any subexpression in evaluation position of <program>") is
   cut the same way.
   `goose.pp.compactWP.post` (default true): a big postcondition that is an
   application of a constant (`forPostcondition s E body inv`, inside loops) is
   printed `forPostcondition …` (`goose.pp.compactWP.postSize`, default 60 nodes).
   `…` (not Lean's `⋯`) marks what this module elided.

`set_option goose.pp.compactWP false` (or `goose.pp.goStrings false`, ...) shows the full
term again, for a file, a declaration (`set_option ... in theorem ...`) or a tactic block
(`set_option goose.pp.compactWP false in tac`).
-/
import Perennial.Golang.Theory.Display
import Tools.WordGuard
import Perennial.Std.ByteString

namespace GooseCompact

open Lean PrettyPrinter Delaborator SubExpr Meta

register_option goose.pp.compactWP : Bool := {
  defValue := true
  descr := "print only the next statements of the program in `WP e {{ Φ }}`" }
register_option goose.pp.compactWP.stmts : Nat := {
  defValue := 4
  descr := "statements of the program shown in `WP e {{ Φ }}` (goose.pp.compactWP)" }
register_option goose.pp.compactWP.inner : Nat := {
  defValue := 1
  descr := "statements shown per nested block (if-branch, function body) (goose.pp.compactWP)" }
register_option goose.pp.compactWP.depth : Nat := {
  defValue := 2
  descr := "nesting depth of blocks shown (goose.pp.compactWP)" }
register_option goose.pp.compactWP.post : Bool := {
  defValue := true
  descr := "print a big postcondition `forPostcondition a b c …` of a WP as `forPostcondition …`" }
register_option goose.pp.compactWP.postSize : Nat := {
  defValue := 60
  descr := "postconditions with more term nodes than this are elided (goose.pp.compactWP.post)" }
register_option goose.pp.goStrings : Bool := {
  defValue := true
  descr := "print a literal list of printable bytes `[97#8, 98#8]` as `go!\"ab\"`" }
register_option goose.pp.lets : Bool := {
  defValue := true
  descr := "print the GooseLang abbreviations Let/Lam/Seq with the let:/λ:/;; notation" }

/-- Printed for what is elided (display only; not valid input). It is not Lean's `⋯`
(an omitted proof or deep term), so that tools can tell the two apart. -/
syntax (name := elidedStx) "…" : term

/-- The elided rest of a program (display only). -/
def elided [Perennial.FfiSyntax] : Perennial.Expr := Perennial.Expr.Var "⋯"

@[delab app.GooseCompact.elided]
def delabElided : Delab := do `(…)

/-! ## Truncating a GooseLang program

The GooseLang constructors and abbreviations take leading instance arguments
(`[FfiSyntax]`); `xargs? e n k` matches an application of `n` and returns its last `k`
arguments, `rebuild e new` replaces them. -/

private def xargs? (e : Lean.Expr) (n : Name) (k : Nat) : Option (Array Lean.Expr) :=
  if e.isAppOf n && e.getAppNumArgs ≥ k then
    let a := e.getAppArgs
    some (a.extract (a.size - k) a.size)
  else none

private def rebuild (e : Lean.Expr) (new : Array Lean.Expr) : Lean.Expr :=
  let a := e.getAppArgs
  mkAppN e.getAppFn (a.extract 0 (a.size - new.size) ++ new)

structure Cfg where
  inner : Nat
  depth : Nat
  elided : Lean.Expr

/-- `e` as a lambda `Rec BAnon x body` / `Lam x body`: `(body, rebuild)`. -/
private def asLam? (e : Lean.Expr) : Option (Lean.Expr × (Lean.Expr → Lean.Expr)) :=
  match xargs? e ``Perennial.Expr.Rec 3 with
  | some a =>
    if a[0]!.isAppOf ``Perennial.Binder.BAnon || a[0]!.isConstOf ``Perennial.Binder.BAnon then
      some (a[2]!, fun b => rebuild e #[a[0]!, a[1]!, b])
    else none
  | none =>
    match xargs? e ``Perennial.Lam 2 with
    | some a => some (a[1]!, fun b => rebuild e #[a[0]!, b])
    | none => none

/-- A statement node `first; rest`: `(first, rest, rebuild first' rest')`. -/
private def asStmt? (e : Lean.Expr) :
    Option (Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr → Lean.Expr)) :=
  if let some a := xargs? e ``Perennial.Let 3 then
    some (a[1]!, a[2]!, fun x y => rebuild e #[a[0]!, x, y])
  else if let some a := xargs? e ``Perennial.Seq 2 then
    some (a[0]!, a[1]!, fun x y => rebuild e #[x, y])
  else if let some a := xargs? e ``Perennial.Expr.App 2 then
    let f := a[0]!
    let x := a[1]!
    match asLam? f with
    | some (body, re) => some (x, body, fun x' b' => rebuild e #[re b', x'])
    | none =>
      -- `exceptionSeq (λ: <>, rest) first`, i.e. `first ;;; rest`
      match xargs? f ``Perennial.Expr.App 2 with
      | some fa =>
        let isExcSeq := match xargs? fa[0]! ``Perennial.Expr.Val 1 with
          | some v => v[0]!.isAppOf ``Perennial.exceptionSeq
          | none => false
        match isExcSeq, asLam? fa[1]! with
        | true, some (body, re) =>
          some (x, body, fun x' b' => rebuild e #[rebuild f #[fa[0]!, re b'], x'])
        | _, _ => none
      | none => none
  else none

private def isGooseCtor (e : Lean.Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n.getPrefix == ``Perennial.Expr || n.getPrefix == ``Perennial.val ||
      n == ``Perennial.Let || n == ``Perennial.Lam || n == ``Perennial.Seq
  | _ => false

/-- Truncate program `e`. The state is the number of statements still to show in the
current block (threaded in evaluation order), `d` the nesting depth. -/
partial def trunc (cfg : Cfg) (d : Nat) (e : Lean.Expr) : StateM Nat Lean.Expr := do
  if !isGooseCtor e then return e
  if let some (first, rest, re) := asStmt? e then
    let first' ← trunc cfg d first
    if (← get) == 0 then return re first' cfg.elided
    modify (· - 1)
    let rest' ← trunc cfg d rest
    return re first' rest'
  -- a nested block: shown with its own (small) budget
  let block (b : Lean.Expr) : StateM Nat Lean.Expr := do
    if d + 1 ≥ cfg.depth then return cfg.elided
    let saved ← get
    set cfg.inner
    let b' ← trunc cfg (d + 1) b
    set saved
    return b'
  if let some a := xargs? e ``Perennial.Expr.If 3 then
    let c ← trunc cfg d a[0]!
    let t ← block a[1]!
    let f ← block a[2]!
    return rebuild e #[c, t, f]
  if let some a := xargs? e ``Perennial.Expr.Rec 3 then
    return rebuild e #[a[0]!, a[1]!, ← block a[2]!]
  if let some a := xargs? e ``Perennial.val.RecV 3 then
    return rebuild e #[a[0]!, a[1]!, ← block a[2]!]
  if let some a := xargs? e ``Perennial.Lam 2 then
    return rebuild e #[a[0]!, ← block a[1]!]
  -- any other constructor: its subterms run now, in order (right to left for `App`)
  let args := e.getAppArgs
  let mut args' := args
  for i in (List.range args.size).reverse do
    args' := args'.set! i (← trunc cfg d args[i]!)
  return mkAppN e.getAppFn args'

/-- `prog` truncated, or `none` if there is nothing to cut (or it is already cut). -/
def truncProgram? (opts : Options) (prog : Lean.Expr) : Option Lean.Expr := do
  guard (prog.isAppOf ``Perennial.Expr.App || prog.isAppOf ``Perennial.Let ||
    prog.isAppOf ``Perennial.Seq || prog.isAppOf ``Perennial.Expr.If)
  guard (prog.find? (·.isAppOf ``elided)).isNone
  -- `elided` with the same `FfiSyntax` instance as the program
  let inst ← prog.getAppArgs[0]?
  let cfg : Cfg := { inner := goose.pp.compactWP.inner.get opts,
                     depth := goose.pp.compactWP.depth.get opts,
                     elided := mkApp (mkConst ``elided) inst }
  let prog' := (trunc cfg 0 prog).run' (goose.pp.compactWP.stmts.get opts) |>.run
  guard (prog' != prog)
  return prog'

/-- `f a₁ … aₙ` printed as `f ⋯` (display only). -/
def elidedArgs {α : Sort _} (x : α) : α := x

@[delab app.GooseCompact.elidedArgs]
def delabElidedArgs : Delab := do
  let e ← getExpr
  let some x := e.getAppArgs[1]? | failure
  let f ← withTheReader SubExpr (fun s => { s with expr := x.getAppFn }) delab
  `($f …)

/-- At most `n` nodes of `e` (`n` if there are more). -/
partial def sizeUpTo (n : Nat) (e : Lean.Expr) : Nat :=
  go e n
where
  go (e : Lean.Expr) (budget : Nat) : Nat :=
    if budget == 0 then 0 else
    match e with
    | .app f a => let b := go f (budget - 1); go a b
    | .lam _ t b _ | .forallE _ t b _ => let r := go t (budget - 1); go b r
    | .letE _ t v b _ => go b (go v (go t (budget - 1)))
    | .mdata _ b | .proj _ _ b => go b (budget - 1)
    | _ => budget - 1

/-- The postcondition of a `WP`: a big application of a constant (`forPostcondition …`,
whose arguments repeat the loop invariant and the frame) is printed `forPostcondition …`.
A variable `Φ` or a continuation `fun v => WP …` is kept (the inner `WP` is compacted). -/
def compactPost? (opts : Options) (post : Lean.Expr) : Option Lean.Expr := do
  guard (goose.pp.compactWP.post.get opts)
  guard post.getAppFn.isConst
  guard !(post.isAppOf ``elidedArgs)
  guard (post.getAppNumArgs > 0)
  guard (sizeUpTo (goose.pp.compactWP.postSize.get opts + 1) post == 0)   -- more nodes than that
  -- the type argument of `elidedArgs` is never looked at (display only)
  return mkApp2 (.const ``elidedArgs [.zero]) (.sort .zero) post

/-- `WP e {{ Φ }}` with `e` truncated (and a big postcondition elided). -/
@[delab app.Iris.Wp.wp]
def delabWpCompact : Delab := do
  let opts ← getOptions
  unless goose.pp.compactWP.get opts do failure
  let e ← getExpr
  unless e.getAppNumArgs == 9 do failure
  let a := e.getAppArgs
  let prog? := truncProgram? opts a[7]!
  let post? := compactPost? opts a[8]!
  if prog?.isNone && post?.isNone then failure
  let a := (a.set! 7 (prog?.getD a[7]!)).set! 8 (post?.getD a[8]!)
  withTheReader SubExpr (fun s => { s with expr := mkAppN e.getAppFn a }) delab

/-- A whole program printed on its own (e.g. in the `wp_apply: cannot apply ... to any
subexpression in evaluation position of <program>` error) is truncated the same way. -/
@[delab app.Perennial.Expr.App, delab app.Perennial.Let, delab app.Perennial.Seq,
  delab app.Perennial.Expr.If]
def delabProgramRoot : Delab := do
  let opts ← getOptions
  unless goose.pp.compactWP.get opts do failure
  unless (← getPos) == Pos.root do failure
  let some prog' := truncProgram? opts (← getExpr) | failure
  withTheReader SubExpr (fun s => { s with expr := prog' }) delab

/-! ## Byte strings -/

private def byteLit? (e : Lean.Expr) : Option Nat :=
  if e.isAppOfArity ``BitVec.ofNat 2 then
    match (e.getArg! 0).nat?, (e.getArg! 1).nat? with
    | some 8, some n => some n
    | _, _ => none
  else none

private partial def byteList? (e : Lean.Expr) (acc : Array Nat) : Option (Array Nat) :=
  if e.isAppOfArity ``List.nil 1 then some acc
  else if e.isAppOfArity ``List.cons 3 then
    match byteLit? (e.getArg! 1) with
    | some n => byteList? (e.getArg! 2) (acc.push n)
    | none => none
  else none

@[delab app.List.cons]
def delabGoString : Delab := do
  unless goose.pp.goStrings.get (← getOptions) do failure
  let some bs := byteList? (← getExpr) #[] | failure
  unless bs.all (fun b => 32 ≤ b && b < 127) do failure
  let s := String.ofList (bs.toList.map Char.ofNat)
  `(go!$(Syntax.mkStrLit s))

/-! ## Let / Lam / Seq -/

private def withExpr (e : Lean.Expr) : Delab := withTheReader SubExpr (fun s => { s with expr := e }) delab

/-- `Let x a b` as the `App (Rec BAnon x b) a` it abbreviates, printed `let: x := a in b`. -/
@[delab app.Perennial.Let]
def delabLet : Delab := do
  unless goose.pp.lets.get (← getOptions) do failure
  let e ← getExpr
  let some a := xargs? e ``Perennial.Let 3 | failure
  let some inst := e.getAppArgs[0]? | failure
  let anon := mkConst ``Perennial.Binder.BAnon
  withExpr (mkAppN (mkConst ``Perennial.Expr.App) #[inst,
    mkAppN (mkConst ``Perennial.Expr.Rec) #[inst, anon, a[0]!, a[2]!], a[1]!])

@[delab app.Perennial.Seq]
def delabSeq : Delab := do
  unless goose.pp.lets.get (← getOptions) do failure
  let e ← getExpr
  let some a := xargs? e ``Perennial.Seq 2 | failure
  let some inst := e.getAppArgs[0]? | failure
  let anon := mkConst ``Perennial.Binder.BAnon
  withExpr (mkAppN (mkConst ``Perennial.Expr.App) #[inst,
    mkAppN (mkConst ``Perennial.Expr.Rec) #[inst, anon, anon, a[1]!], a[0]!])

@[delab app.Perennial.Lam]
def delabLam : Delab := do
  unless goose.pp.lets.get (← getOptions) do failure
  let e ← getExpr
  let some a := xargs? e ``Perennial.Lam 2 | failure
  let some inst := e.getAppArgs[0]? | failure
  withExpr (mkAppN (mkConst ``Perennial.Expr.Rec) #[inst, mkConst ``Perennial.Binder.BAnon, a[0]!, a[1]!])

end GooseCompact
