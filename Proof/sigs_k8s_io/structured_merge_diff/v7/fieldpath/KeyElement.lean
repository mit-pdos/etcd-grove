/-
`fieldpath.KeyElement`: proved over its callees' specs
(notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.KeyElement
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.KeyElement.wp_proof :
    fieldpath.KeyElement.spec (GF := GF) := fun s fl => by
  wp_start as ⟨#Hfl, %hok⟩
  iapply wp_fupd
  wp_auto
  ipersist l
  imodintro
  iapply HΦ
  unfold isPE
  isplit
  · ipureintro; exact ⟨rfl, hok⟩
  · iexists s; iframe l Hfl

end proof

end smd
end EtcdGrove
end Perennial
