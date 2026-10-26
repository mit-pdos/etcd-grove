/-
Proof of `Spec/k8s_io/client_go/util/workqueue/Typed__Len.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.Typed__Len
public import Spec.k8s_io.client_go.util.workqueue.queue__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem Typed.Len.wp_proof
    (wp_Len : queue.Len.spec (GF := GF) (hG := hG)) :
    Typed.Len.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as #Hq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  ihave #HL := isCond_L _ _ $$ Hcv
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iNamedSuffix HI "_i"
  ihave %Hql := ownFifo_length_lt _ _ $$ Hfifo_i
  (try wp_auto)
  wp_apply wp_Len $$ [$Hfifo_i] as Hfifo_i
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
  · inext; iunfold qLockInv; iexists σ, drain; iframe; ipureintro; exact Hwf_i
  iapply HΦ
  ipureintro
  word

end proof

end workqueue
end EtcdGrove
end Perennial
