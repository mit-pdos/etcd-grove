/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newLogUnaryInterceptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryRequestStats

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.newLogUnaryInterceptor.wp_proof
    (wp_Logger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (wp_log : v3rpc.logUnaryRequestStats.spec (GF := GF) (hG := hG)) :
    v3rpc.newLogUnaryInterceptor.spec (GF := GF) (hG := hG) := by
  intro s lg wd
  wp_start as ⟨#Hlg, %Hlgn, #Hwd⟩
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_alloc_auto
  irename : (s_ptr ↦ s : IProp GF) => Hs
  ipersist Hs
  wp_auto
  iapply HΦ
  iintro !> %Q
  unfold srvInterceptorOk
  iintro !> %ci %cd %req %info %h %Ψ HR #Hctx #Hrc #Hinfo #HQ Hk
  iunfold srvInterceptorCall
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply time.wp_Now as %now -
  icases Hk with ⟨Hk, -⟩
  iunfold srvHandlerCall at Hk
  wp_bind (App (App (Val #h) _) _)
  iapply (wp_wand (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
    (srvLgReader s -∗ Ψ v)))) $$ Hk
  iintro %v ⟨%resp, %err, %Hv, HΨ⟩
  subst Hv
  wp_auto
  wp_apply wp_Logger s lg $$ [HR] as ⟨-, HR⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  wp_if_destruct
  · exact absurd rfl Hlgn
  wp_apply wp_log $$ []
  · iframe #; ipureintro; exact Hlgn
  iapply HΨ
  iexact HR

end proof

end EtcdGrove
end Perennial
