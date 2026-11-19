/-
`typed.reconcileWithSchemaWalker.finished`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finished
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Perennial.Spec.sync.Pool__Put

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
variable [package_sem : typed.Assumptions]

theorem typed.reconcileWithSchemaWalker.finished.wp_proof
    (h_sync_Pool_Put : _root_.Perennial.sync.Pool.Put.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.finished.spec (GF := GF) :=
    fun w sc S st ps fs tv rem add sp => by
  wp_start as ⟨Hcore, Hsp, %Hat⟩
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨-, -, -, -, -, -, #Pv⟩
  unfold rwCore
  icases Hcore with ⟨%tr, Hw, -, -, -⟩
  wp_auto
  wp_apply h_sync_Pool_Put (globalAddr typed.fmPool) typed.rwNewV iprop(True)
    (pooledAs typed.reconcileWithSchemaWalker.ty rwPooled) $$ [Hw Hsp]
  · iframe #
    unfold pooledAs rwPooled
    iexists w
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Hw
    isplitr
    · ipureintro; simp [Hat]
    iexact Hsp
  iapply HΦ
  itrivial

end proof

end smd
end EtcdGrove
end Perennial
