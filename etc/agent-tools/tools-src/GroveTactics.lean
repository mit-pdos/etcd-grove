/-
Proof-writing helpers for Perennial proofs that do not need changes to Perennial:

* `wp_bounds` — discharge the bounds check `if c then … else Panic …` that slice
  indexing/slicing leaves in the program, proving `c` with `word` (after splitting the
  conjunctions among the hypotheses).
* `wp_load_frac` / `wp_auto_frac` — load a struct field through a *fractional* struct
  points-to `l ↦{dq} v` (`wp_auto` only finds the field when `dq` is `DFrac.own 1`).
* `inorm` / `iframe_norm` — normalise both the hypotheses and the goal of an Iris goal with
  the `inorm` simp set before framing (`zero_val Bool` vs `false`, `sint.nat (W64 0)`,
  `take`/`drop`/`map` of `[]`, `Option.getD` …), so syntactic mismatches stop blocking
  `iframe`/`iexact`.
* `wp_run` — `wp_auto` plus anonymous allocations (unnamed Go results) and fractional loads.
* `wp_ptr_method` — step into a value method called through a pointer.
* `timed tac` — run `tac` and print its wall time.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Theory

namespace EtcdGrove
namespace Tactics

open Lean Elab Tactic Meta

/-! ## `split_ands_hyps`: `h : a ∧ b` in the context gives `h.1 : a`, `h.2 : b` -/

/-- Add the conjuncts of every conjunction in the local context (recursively) as new
hypotheses (the conjunction itself is kept). -/
elab "split_ands_hyps" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut work : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``And 2 then work := work.push (d.toExpr, ty)
  let mut fuel := 64
  while h : work.size > 0 do
    if fuel == 0 then break
    fuel := fuel - 1
    let (pf, ty) := work[work.size - 1]
    work := work.pop
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    let pa := mkApp3 (mkConst ``And.left) a b pf
    let pb := mkApp3 (mkConst ``And.right) a b pf
    for (p, t) in [(pa, a), (pb, b)] do
      let (_, g') ← (← g.assert `hand t p).intro1P
      g := g'
      if t.isAppOfArity ``And 2 then work := work.push (p, t)
  replaceMainGoal [g]

/-- The bounds solver of `wp_bounds`: `word`, then `word` after splitting conjunctions,
then `decide`. -/
macro "bounds_solve" : tactic =>
  `(tactic| first
    | (constructor <;> first | word | (split_ands_hyps; word) | decide | assumption)
    | word | (split_ands_hyps; word) | decide | assumption)

/-! ## `wp_bounds` -/

def isPanicName : Name → Bool
  | .str _ s => s.startsWith "Panic" || s.startsWith "panic"
  | _ => false

/-- Does `e` mention a constant whose last name component is `Panic`/`panic`? -/
def mentionsPanic (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .const n _ => isPanicName n
    | _ => false).isSome

/-- The `ite`s with a closed condition whose else branch panics, in traversal order. -/
def panicItes (e : Expr) : Array Expr := Id.run do
  let mut out := #[]
  let mut todo := #[e]
  while h : todo.size > 0 do
    let s := todo[todo.size - 1]
    todo := todo.pop
    if s.isAppOfArity ``ite 5 && !(s.getArg! 1).hasLooseBVars && mentionsPanic (s.getArg! 4) then
      out := out.push s
    -- push children in reverse so that the traversal is left to right
    match s with
    | .app f a => todo := todo.push a |>.push f
    | .lam _ t b _ => todo := todo.push b |>.push t
    | .forallE _ t b _ => todo := todo.push b |>.push t
    | .letE _ t v b _ => todo := todo.push b |>.push v |>.push t
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- Rewrite one bounds check `ite c t (… Panic …)` to `t`, proving `c` with `tac`.
Returns `false` if no such `ite` has a condition `tac` proves. -/
def boundsStep (tac : Syntax) (all : Bool) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let mut done := false
  for ite in panicItes tgt do
    if done && !all then break
    let c := ite.getArg! 1
    let hc ← mkFreshExprSyntheticOpaqueMVar c
    let ok ← try
        let gs ← Tactic.run hc.mvarId! (evalTactic tac)
        pure gs.isEmpty
      catch _ => pure false
    unless ok do
      if all then continue
      throwError "wp_bounds: could not prove the bounds condition{indentExpr c}"
    let eq := mkAppN (mkConst ``if_pos [ite.getAppFn.constLevels!.head!])
      #[c, ite.getArg! 2, ← instantiateMVars hc, ite.getArg! 0, ite.getArg! 3, ite.getArg! 4]
    let g ← getMainGoal
    let r ← g.rewrite (← instantiateMVars (← g.getType)) eq
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)
    done := true
  return done

/-- `wp_bounds` discharges the next bounds check `if c then e else Panic "…"` of the
program (slice index, slicing, `copy`, …): proves `c` with `word` (also after splitting the
conjunctions among the hypotheses, and splitting `c` itself) and rewrites the `if` to `e`.
`wp_bounds using tac` proves `c` with `tac` instead; `wp_bounds*` rewrites every
bounds check whose condition is provable. -/
syntax "wp_bounds" ("*")? (" using " tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| wp_bounds $[*%$star]? $[using $tac]?) => do
    let tac ← match tac with
      | some t => `(tactic| ($t))
      | none => `(tactic| bounds_solve)
    let ok ← boundsStep tac star.isSome
    unless ok do throwError "wp_bounds: no bounds check `if _ then _ else Panic _` in the goal"

/-! ## `wp_load_frac`: load through a fractional (struct) points-to -/

section load_frac
open Perennial Qq Iris Iris.BI Iris.ProofMode

/-- `iWpLoadStepV` of `Perennial/Golang/Theory/Mem.lean`, but the fraction of the
points-to looked for is taken from each candidate hypothesis `l' ↦{dq} v'` (instead of
being a metavariable, which makes the `Access` search pick the `DFrac.own 1` store
instance of a struct field and fail). -/
def iWpLoadFracStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr)) := do
  let some ((t, l), K, _) ← findEctx wp.e (fun _ e => do
      let some (i, lv) ← isGoInstrApp? e ``GoInstruction.GoLoad | throwError "no"
      let some (_, l) ← isIntoVal? lv | throwError "no"
      return (i.getArg! 1, l))
    | throwIPMError "could not find a load `![t] #l`"
  let GF := (← gooseGSArgs wp.ι)[6]!
  for (_, ivar, _, P) in ← hypsListFor hyps l do
    let Pi ← instantiateMVars P
    -- the points-to may be under a name (`"H" ∷ l ↦{dq} v`)
    let some pt := Pi.find? (·.isAppOfArity ``typedPointsto 6) | continue
    let dq0 := pt.getArg! 5
    let saved ← saveState
    let (A, V, inst, v, dq) ← mkTypedPointstoMVars GF l none none (some dq0)
    if let some (hacc, P') ← synthAccess A A P then
      if ← isDefEq P' P then
        let r := hyps.remove true ivar
        let v ← instantiateMVars v
        let vv ← instantiateMVars (← mkAppOptM ``GoGlobalContext.intoVal
          #[none, none, some (← instantiateMVars V), some v])
        let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.Expr.Val) wp.ext vv)
        let k := fun (h : Lean.Expr) => do
          let V ← instantiateMVars V
          let inst ← instantiateMVars inst
          wp.mkAppNamed ``Perennial.tac_wp_load
            [("Δ", ehyps), ("Δ'", r.e'), ("Φ", wp.Φ),
             ("V", V), ("t", t), ("K", wp.quoteK K), ("l", l), ("v", v),
             ("dq", ← instantiateMVars dq), ("p", r.p), ("P", P),
             ("s", wp.s), ("E", wp.E), ("tpt", inst), ("hacc", hacc),
             ("hsplit", r.pf), ("!h", h)]
        return ⟨ehyps, hyps, filled, k⟩
    restoreState saved
  throwIPMError "wp_load_frac: no fractional points-to in context covering the address {l}"

/-- `wp_load_frac` performs the next load `![t] #l` using a hypothesis `l' ↦{dq} v'`
that covers `l` with its own fraction `dq` — in particular a struct field
`l'.[S, "f"]` through a fractional struct points-to `l' ↦{dq} v'`, which `wp_load` and
`wp_auto` miss when `dq` is not `DFrac.own 1`. The hypothesis is kept. -/
elab "wp_load_frac" : tactic =>
  runTacticGooseWp `wp_load_frac fun mvar g wp => do
    let ⟨_, hyps', e', k⟩ ← iWpLoadFracStep g.hyps wp
    mvar.assign (← k (← iWpFinish hyps' { wp with e := e' }))

end load_frac

/-- `wp_auto_frac`: `wp_auto`, and whenever it stops at a load it could not do, a
`wp_load_frac` and `wp_auto` again (fails only if neither makes progress). -/
macro "wp_auto_frac" : tactic =>
  `(tactic| ((first | wp_auto | wp_load_frac); repeat (first | wp_auto | wp_load_frac)))

/-- `wp_run`: `wp_auto`, plus the steps it leaves to the user — anonymous allocations
(`wp_alloc_anon`: Go functions with unnamed results allocate them without a name) and
loads through fractional points-tos (`wp_load_frac`) — until none applies. Fails only if
nothing applies. -/
macro "wp_run" : tactic =>
  `(tactic| ((first | wp_auto | wp_alloc_anon | wp_load_frac); repeat (first | wp_auto | wp_alloc_anon | wp_load_frac)))

/-- `wp_ptr_method`: step into a value method called through a pointer (`p.m(…)` where
`m` has a value receiver, which Goose compiles to the pointer method wrapper that loads
`*p`): resolves the method (`wp_method_call`), enters the wrapper (`wp_call`) and loads the
receiver (`wp_auto_frac`, also through a fractional points-to), so that the value method's
spec can be `wp_apply`'d next. -/
macro "wp_ptr_method" : tactic =>
  `(tactic| (wp_method_call; wp_call; wp_auto_frac))

/-! ## `timed tac`: run `tac` and report its wall time (ms) as an info message -/

elab "timed " tac:tactic : tactic => do
  let t0 ← IO.monoNanosNow
  evalTactic tac
  let t1 ← IO.monoNanosNow
  logInfo m!"timed: {(t1 - t0) / 1000000} ms"

/-! ## `inorm`: the normalisation simp set used before framing -/

open Perennial in
theorem zero_val_bool_eq : zero_val Bool = false := rfl
open Perennial in
theorem sint_nat_zero : sint.nat (W64 0) = 0 := rfl
open Perennial in
theorem sint_Z_toNat (x : w64) : (sint.Z x).toNat = sint.nat x := rfl

/-- `inorm`: normalise the whole goal (Iris hypotheses and conclusion) with a small simp
set (`zero_val`, `sint.nat` of literals, `take`/`drop`/`map`/`append` of `[]`, `Option`
projections of `some`/`none`) and the extra lemmas given, so that `iframe`/`iexact` see
the same syntactic form on both sides. Never fails. Do not use it on a goal whose
conclusion is still a `WP` (simp would also rewrite inside the program). -/
syntax "inorm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| inorm $[[$ls,*]]?) => do
    let base : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[
      ← `(Lean.Parser.Tactic.simpLemma| zero_val_bool_eq),
      ← `(Lean.Parser.Tactic.simpLemma| sint_nat_zero),
      ← `(Lean.Parser.Tactic.simpLemma| sint_Z_toNat),
      ← `(Lean.Parser.Tactic.simpLemma| List.take_nil),
      ← `(Lean.Parser.Tactic.simpLemma| List.drop_nil),
      ← `(Lean.Parser.Tactic.simpLemma| List.take_zero),
      ← `(Lean.Parser.Tactic.simpLemma| List.drop_zero),
      ← `(Lean.Parser.Tactic.simpLemma| List.map_nil),
      ← `(Lean.Parser.Tactic.simpLemma| List.nil_append),
      ← `(Lean.Parser.Tactic.simpLemma| List.append_nil),
      ← `(Lean.Parser.Tactic.simpLemma| List.map_append),
      ← `(Lean.Parser.Tactic.simpLemma| List.map_cons),
      ← `(Lean.Parser.Tactic.simpLemma| List.map_take),
      ← `(Lean.Parser.Tactic.simpLemma| List.map_drop),
      ← `(Lean.Parser.Tactic.simpLemma| List.map_set),
      ← `(Lean.Parser.Tactic.simpLemma| List.map_dropLast),
      ← `(Lean.Parser.Tactic.simpLemma| List.dropLast_nil),
      ← `(Lean.Parser.Tactic.simpLemma| Option.getD_some),
      ← `(Lean.Parser.Tactic.simpLemma| Option.getD_none),
      ← `(Lean.Parser.Tactic.simpLemma| Option.map_some),
      ← `(Lean.Parser.Tactic.simpLemma| Option.map_none),
      ← `(Lean.Parser.Tactic.simpLemma| Option.isSome_some),
      ← `(Lean.Parser.Tactic.simpLemma| Option.isSome_none),
      ← `(Lean.Parser.Tactic.simpLemma| Bool.not_true),
      ← `(Lean.Parser.Tactic.simpLemma| Bool.not_false)]
    let extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := match ls with
      | some ls => ls.getElems.map (⟨·.raw⟩)
      | none => #[]
    let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (base ++ extra)
    `(tactic| simp (config := { failIfUnchanged := false }) only [$all,*])

/-- `iframe_norm [lemmas]`: `inorm [lemmas]` and then `iframe`. -/
syntax "iframe_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| iframe_norm [$ls,*]) => `(tactic| (inorm [$ls,*]; iframe))
  | `(tactic| iframe_norm) => `(tactic| (inorm; iframe))

end Tactics
end EtcdGrove
