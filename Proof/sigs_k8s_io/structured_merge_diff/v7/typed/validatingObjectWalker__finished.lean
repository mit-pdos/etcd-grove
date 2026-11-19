/-
`typed.validatingObjectWalker.finished`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finished
public import Perennial.Spec.sync.Pool__Put

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

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

theorem typed.validatingObjectWalker.finished.wp_proof
    (h_sync_Pool_Put : _root_.Perennial.sync.Pool.Put.spec (GF := GF)) :
    typed.validatingObjectWalker.finished.spec (GF := GF) := fun w sc S st => by
  wp_start as Hown
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨-, -, -, -, -, #Pv, -⟩
  unfold vwOwn vwCore
  icases Hown with ⟨%sp, ⟨%tr, Hw, -, -, -⟩, Hsp, Ha⟩
  wp_auto
  wp_apply h_sync_Pool_Put (globalAddr typed.vPool) typed.vwNewV iprop(True)
    (pooledAs typed.validatingObjectWalker.ty vwPooled) $$ [Hw Hsp Ha]
  · iframe #
    unfold pooledAs vwPooled
    iexists w
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Hw Hsp
    iright; iexact Ha
  iapply HΦ
  itrivial

end proof

end smd
end EtcdGrove
end Perennial
