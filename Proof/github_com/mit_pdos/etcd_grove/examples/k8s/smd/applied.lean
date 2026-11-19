/-
`applied` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.applied
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem applied.wp_proof
    (wp_NewSet : smd.fieldpath.NewSet.spec (GF := GF))
    (wp_NewVersionedSet : smd.fieldpath.NewVersionedSet.spec (GF := GF)) :
    applied.spec (GF := GF) := fun s dq ss ps => by
  wp_start as ⟨Hs, Hps⟩
  wp_auto
  wp_apply wp_NewSet $$ [$Hs $Hps] as %p ⟨Hs, Hp⟩
  wp_apply wp_NewVersionedSet
  iapply HΦ
  iframe Hs
  unfold ownVSet
  iexists p
  isplitr
  · ipureintro; rfl
  simp only [k8s_smd.applied]
  iexact Hp

end proof

end k8s_smd
end EtcdGrove
end Perennial
