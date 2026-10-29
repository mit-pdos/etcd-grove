/-
Proof of `Spec/k8s_io/client_go/util/workqueue/Typed__ShuttingDown.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.Typed__ShuttingDown

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem Typed.ShuttingDown.wp_proof : Typed.ShuttingDown.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as #Hq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  ihave #HL := isCond_L _ _ $$ Hcv
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iNamedSuffix HI "_i"
  (try wp_auto)
  cases hsd : σ.shuttingDown
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
    · inext; iunfold qLockInv; iexists σ, drain; rw [hsd]; iframe; ipureintro; exact Hwf_i
    iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [sdGhost, ↓reduceIte]
    icases Hsdg_i with #Hsdlb
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i]
    · inext; iunfold qLockInv; iexists σ, drain; rw [hsd]; simp only [sdGhost, ↓reduceIte]
      iframe; iframe #; ipureintro; exact Hwf_i
    iapply HΦ; simp only [↓reduceIte]; iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
