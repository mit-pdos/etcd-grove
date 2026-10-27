/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__ShutDown.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__ShutDown
public import Spec.k8s_io.client_go.util.workqueue.Typed__ShutDown

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

theorem delayingType.ShutDown.wp_proof
    (wp_ShutDown : Typed.ShutDown.spec (GF := GF) (hG := hG)) :
    delayingType.ShutDown.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as #Hq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  wp_auto
  ipersist q
  wp_apply sync.Once.wp_Do $$ [$Honce]
  · iintro !> %Φ' ⟨HP, Htoks⟩ HΦ'
    wp_auto
    wp_apply wp_ShutDown $$ [$Htyped $Htoks] as ⟨#Hsdlb, -⟩
    wp_apply wp_broadcast_chan_close $$ [$HP] as -
    · iexact Hsdlb
    iunfold isTickerI at Htk
    icases Htk with ⟨%ti, %Hti, #HC, #HS⟩
    subst Hti
    wp_auto
    wp_apply HS
    iapply HΦ'; iexact Hsdlb
  iintro #Hsd
  wp_auto
  iapply HΦ; iexact Hsd

end proof

end workqueue
end EtcdGrove
end Perennial
