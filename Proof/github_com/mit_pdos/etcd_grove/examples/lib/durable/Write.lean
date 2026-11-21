/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/durable/Write.lean`. Lean-first (no
Rocq counterpart): `Write` is the extension's `"Write"` (its trusted model), whose atomic spec is
`wp_DurableWrite_atomic`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write
import Perennial.GooseLang.NotCrashed

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

/-- (2026-11-21) The extension's `"Write"` is atomic: it takes one step, to a value
(`DurableStep`). -/
private instance durableWrite_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (ExternalOp durableExt.name "Write" (Val v)) :=
  goose_atomic a (fun _ _ e' _ _ hb => by
      cases hb with
      | ExternalOpS _ _ _ _ _ _ hst =>
        obtain ⟨_, _, _, hst', rfl⟩ := (extStep_named _ _ _ _ _).1 hst
        have h2 := (HasExt.step_iff ..).1 hst'
        obtain ⟨-, _, _, -, rfl, -⟩ := h2
        rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

theorem github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.wp_proof :
    github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec (GF := GF) (hG := hG) :=
  fun o name data h => by
  iintro %Φ HAU
  wp_func_call
  unfold github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.impl
  wp_pures
  -- (2026-11-21) the token at the write's step (`wp_atomic_nc`), lent to the update's opening
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := ∅) _ _ rfl)
  iintro Hnc
  imod HAU $$ Hnc with ⟨Hnc, %fs, Hown, Hcl⟩
  imodintro
  iframe Hnc
  iapply wp_DurableWrite_atomic (E := ∅) o name data h (fun v => iprop(|={∅,⊤}=> Φ v))
  imodintro
  iexists fs
  iframe Hown
  iintro Hown
  imodintro
  iapply Hcl $$ Hown

end proof

end Perennial
