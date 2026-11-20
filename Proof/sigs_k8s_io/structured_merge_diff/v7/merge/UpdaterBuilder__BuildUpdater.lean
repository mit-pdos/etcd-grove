/-
`merge.UpdaterBuilder.BuildUpdater`: a fresh `Updater` literal of the builder's fields, made
read-only (`isUpdater_intro`). Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.UpdaterBuilder__BuildUpdater
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

theorem merge.UpdaterBuilder.BuildUpdater.wp_proof :
    merge.UpdaterBuilder.BuildUpdater.spec (GF := GF) := fun b dq ub => by
  wp_start as Hb
  iapply wp_fupd
  icases typedPointsto_not_null_dup _ _ _ $$ Hb with ⟨Hb, %hbnn⟩
  iStructNamed Hb
  wp_auto
  ipersist «$r0»
  imodintro
  iapply HΦ
  isplitl [Converter IgnoredFields IgnoreFilter ReturnInputOnNoop]
  · iapply typedPointsto_combine _ _ _ hbnn
    simp only [typedPointstoDef]
    iframe
  iapply (isUpdater_intro_law_holds _ _ _ _ _)
  iexact «$r0»

end proof

end smd
end EtcdGrove
end Perennial
