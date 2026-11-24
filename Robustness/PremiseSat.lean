/-
Lean-first (no Rocq counterpart).

# Satisfiability witnesses of a top-level statement's premises

A top-level statement (`def X.spec : Prop`, `Spec/**/TopLevelRobustness.lean`) is
`∀ binders, Robust crashing stable g threads bound`. If its premises, together with `Robust`'s own
antecedents (fresh machines in their extensions' initial states, `RobustStart`), cannot all hold,
the statement is vacuous. `premise_sat% X.spec` is the proposition that they can:
`etc/premise-witness.py` (in `etc/gates.sh` and CI) requires, for each such statement, a theorem

    theorem X.premisesSat : premise_sat% X.spec := …

in `Proof/<the example's path>/TopLevelWitness.lean` (a part's under its root), which the build
checks. The proposition is computed from `X.spec`'s definition, so it cannot drift from the
statement. Walking `X.spec`'s `∀` binders in order:

* the definition's own parameters and the instance binders (`[sem : go.Semantics]`, the packages'
  `Assumptions`, …) stay universal: the witness must work for every instance;
* data binders (`σ`, `g`, `k`, `dir`, …) become `∃`;
* premises (binders whose type is a `Prop`) become conjuncts;
* the conclusion `Robust crashing stable g threads bound` becomes `RobustStart crashing stable g`.

Some binders are **left out** (with every binder whose type depends on one left out; a binder
kept may not depend on one left out):
* a premise that mentions `HeapGS` or a constant of the namespace `Iris`: an Iris contract (class
  (a) of `notes/` and the coordinator's survey), which rule 36 turns into per-function axioms, not
  witnessed here;
* the binders named in `without [h₁, …]`: each must be listed, with its reason, in
  `etc/premise-witness-baseline.txt` (the script checks it), e.g. an opaque environment
  proposition (`authRecordsFit`), which no Lean proof can establish.

Untrusted: a witness only adds evidence; nothing uses it.
-/
module

public import Lean
public import Robustness.Statement

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

section start
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- **`Robust`'s antecedents** (`Robust`, `Statement.lean`): every machine of `crashing ++ stable`
is a fresh Go process with the context `lctx`, in its extensions' initial state, on the shared state
`g`, itself in its extensions' initial state. A statement whose premises cannot hold together with
these is vacuous. -/
def RobustStart [lctx : GoLocalContext] (crashing stable : List (Expr × state)) (g : GlobalState) :
    Prop :=
  (∀ m, m ∈ crashing ++ stable → Fresh lctx m.2) ∧ extsInitGlobal g ∧
    (∀ m, m ∈ crashing ++ stable → extsInitLocal m.2 g)

/-- A fresh process with the context `lctx` and the extensions' local state `w`. -/
def freshState [lctx : GoLocalContext] (w : ExtsLocalState exts) : state :=
  { heap := ∅, goState := ⟨lctx, ∅⟩, world := w, threads := 1 }

theorem fresh_freshState [lctx : GoLocalContext] (w : ExtsLocalState exts) :
    Fresh lctx (freshState w) :=
  ⟨rfl, rfl, rfl⟩

/-- `RobustStart` of one machine. -/
theorem robustStart_one [lctx : GoLocalContext] {e : Expr} {σ : state} {g : GlobalState}
    (hf : Fresh lctx σ) (hg : extsInitGlobal g) (hl : extsInitLocal σ g) :
    RobustStart [] [(e, σ)] g ∧ RobustStart [(e, σ)] [] g := by
  refine ⟨⟨?_, hg, ?_⟩, ⟨?_, hg, ?_⟩⟩ <;> intro m hm <;> simp at hm <;> subst hm <;> assumption

end start

open Lean Meta Elab Term

/-- Whether `t` mentions `HeapGS` or a constant of the namespace `Iris` (an Iris premise). -/
meta def isIrisPremise (t : Expr) : Bool :=
  (t.find? fun e => match e with
    | .const n _ => n == ``Perennial.HeapGS || (`Iris).isPrefixOf n
    | _ => false).isSome

/-- The proposition `premise_sat%` builds from the body `e` of a statement (see the file header):
`drop` are the names given in `without`, `dropped` the binders left out so far. Returns the
proposition and the names of the binders it left out. -/
meta partial def premiseSatOf (drop : List Name) (dropped : Array FVarId) (e : Expr) :
    MetaM (Expr × Array Name) := do
  let e ← instantiateMVars e
  match e with
  | .forallE n t b bi =>
    withLocalDecl n bi t fun x => do
      let b' := b.instantiate1 x
      let tIsProp ← isProp t
      let dep := t.hasAnyFVar (dropped.contains ·)
      if dep || drop.contains n || (tIsProp && isIrisPremise t) then
        let (rest, names) ← premiseSatOf drop (dropped.push x.fvarId!) b'
        if rest.containsFVar x.fvarId! then
          throwError "premise_sat%: the binder {n} is left out, but what follows depends on it"
        return (rest, names.push n)
      let (rest, names) ← premiseSatOf drop dropped b'
      if bi.isInstImplicit then
        return (← mkForallFVars #[x] rest, names)
      if tIsProp then
        if rest.containsFVar x.fvarId! then
          throwError "premise_sat%: what follows the premise {n} depends on its proof"
        return (mkAnd t rest, names)
      return (← mkAppM ``Exists #[← mkLambdaFVars #[x] rest], names)
  | _ =>
    unless e.isAppOf ``Robustness.Robust do
      throwError "premise_sat%: the statement's conclusion is not `Robust …`:{indentExpr e}"
    let args := e.getAppArgs
    let lvls := e.getAppFn.constLevels!
    return (mkAppN (mkConst ``RobustStart lvls) (args.extract 0 (args.size - 2)), #[])

/-- `premise_sat% X.spec` (optionally `without [h, …]`): the premises of the statement `X.spec`
are satisfiable together with `Robust`'s antecedents (see the file header). -/
syntax (name := premiseSatStx) "premise_sat% " ident (" without " "[" ident,* "]")? : term

@[term_elab premiseSatStx] meta def elabPremiseSat : TermElab := fun stx _ => do
  let declName ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let drop : List Name :=
    if stx[2].isNone then [] else (stx[2][2].getSepArgs.map (·.getId)).toList
  let info ← getConstInfo declName
  let some val := info.value? | throwError "premise_sat%: {declName} has no definition"
  let lvls := info.levelParams.map mkLevelParam
  let val := val.instantiateLevelParams info.levelParams lvls
  lambdaTelescope val fun params body => do
    let (p, names) ← premiseSatOf drop #[] body
    for n in drop do
      unless names.contains n do
        throwError "premise_sat%: {declName} has no binder {n} to leave out"
    mkForallFVars params p

end Robustness
end Perennial

end
