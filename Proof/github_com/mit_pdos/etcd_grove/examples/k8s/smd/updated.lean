/-
`updated`: `NewVersionedSet(NewSet(paths...), version, false)` (`ownSet_persist`). Lean-first
(2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.updated
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Sets

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

theorem updated.wp_proof_of (hPersist : ownSet_persist.law (GF := GF))
    (wp_NewSet : smd.fieldpath.NewSet.spec (GF := GF))
    (wp_NewVersionedSet : smd.fieldpath.NewVersionedSet.spec (GF := GF)) :
    updated.spec (GF := GF) := fun s dq ss ps => by
  wp_start as ⟨Hs, Hps⟩
  wp_auto
  wp_apply wp_NewSet $$ [$Hs $Hps] as %p ⟨Hs, Hp⟩
  imod (hPersist p _) $$ Hp with Hp
  wp_apply (wp_NewVersionedSet p _ version false) $$ [Hp] as %i Hi
  · iexact Hp
  iapply HΦ
  iframe Hs
  unfold k8s_smd.updated
  iexact Hi

theorem updated.wp_proof
    (wp_NewSet : smd.fieldpath.NewSet.spec (GF := GF))
    (wp_NewVersionedSet : smd.fieldpath.NewVersionedSet.spec (GF := GF)) :
    updated.spec (GF := GF) :=
  updated.wp_proof_of ownSet_persist_law_holds wp_NewSet wp_NewVersionedSet

end proof

end k8s_smd
end EtcdGrove
end Perennial
