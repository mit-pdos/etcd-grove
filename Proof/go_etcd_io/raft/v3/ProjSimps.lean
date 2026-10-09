/-
`proj_simps f₁ f₂ …`: projection lemmas for functions that build a record.

For a definition `f : ∀ xs, S` whose result type `S` is a structure and whose body
unfolds to a constructor (a structure instance `{ a := …, b := … }` or an update
`{ s with b := … }`), it adds, for every field `a` of `S`,

    @[simp, word_unfold] theorem f.proj_a : ∀ xs, (f xs).a = <the field's value>

proved by `rfl`. Fields whose value is the same projection of an argument (the
unchanged fields of an update, `(f s).a = s.a`) get a lemma too. If `f`'s body is
not a constructor after unfolding (an `if`, a `match`), the command is an error. For
a structure that extends another, the parent is one field (`f.proj_toParent`), not one
lemma per inherited field; `simp` still reduces through it.

Why: a projection of a record built by a function, like a projection of a literal
record (`{ prev := p, … }.prev`), is an atom that `omega` and `rw` do not see through
(`omega` sees `(inflightsRingOf iv buf).buflen` and `buf.length` as unrelated). With
these lemmas `simp` rewrites such projections away, and so does `word` (whose
preprocessing runs `simp only [word_unfold] at *`), so a proof does not have to know
which `dsimp only [f] at h` to write first. Projections of *literal* records are
reduced by `simp` and `word` without any lemma (notes/decisions.md, "Records in
proofs").
-/
module

public import Lean
public import Perennial.Std.Attrs

@[expose] public section

namespace Perennial.EtcdGrove

open Lean Meta Elab Command

/-- The projection lemmas of `declName`: `(name, type, proof)` per field, or `none` if
its body does not unfold to a constructor. -/
meta def projSimpLemmas (declName : Name) : MetaM (Option (Array (Name × Expr × Expr))) := do
  let info ← getConstInfo declName
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs ty => do
    let ty ← whnfR ty
    let some structName := ty.getAppFn.constName? | return none
    let env ← getEnv
    unless isStructure env structName do return none
    let lhsBase := mkAppN (mkConst declName lvls) xs
    let some body ← unfoldDefinition? lhsBase | return none
    let body ← whnfCore body
    let ctor := getStructureCtor env structName
    unless body.isAppOfArity ctor.name (ctor.numParams + ctor.numFields) do return none
    let fields := getStructureFields env structName
    let mut out := #[]
    for h : i in [0:fields.size] do
      let field := fields[i]
      let val := body.getArg! (ctor.numParams + i)
      let lhs ← mkProjection lhsBase field
      let eq ← mkEq lhs val
      let type ← mkForallFVars xs eq
      let proof ← mkLambdaFVars xs (← mkEqRefl lhs)
      let name := Name.str declName ("proj_" ++ field.toString)
      out := out.push (name, type, proof)
    return some out

/-- See the module docstring. -/
syntax (name := projSimpsCmd) "proj_simps " ident+ : command

@[command_elab projSimpsCmd]
meta def elabProjSimps : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let declName ← liftCoreM <| realizeGlobalConstNoOverload id
    let info ← getConstInfo declName
    let some lemmas ← liftTermElabM (projSimpLemmas declName)
      | throwErrorAt id "proj_simps: {declName} does not unfold to a structure constructor"
    for (name, type, proof) in lemmas do
      liftCoreM <| addDecl <| .thmDecl
        { name, levelParams := info.levelParams, type, value := proof }
      elabCommand (← `(attribute [simp, word_unfold] $(mkIdent name)))

end Perennial.EtcdGrove
