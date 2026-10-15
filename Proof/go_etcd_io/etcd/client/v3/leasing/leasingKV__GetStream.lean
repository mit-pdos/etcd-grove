/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__GetStream.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__GetStream
public import Spec.google_golang_org.grpc.status.Error

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.GetStream.wp_proof
    (hErr : EtcdGrove.status.Error.spec (GF := GF) (hG := hG)) :
    leasingKV.GetStream.spec (GF := GF) (hG := hG) := by
  intro lkv ctx key sl
  wp_start
  wp_auto
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_apply hErr (W32 12) go!"GetStream is not supported by leasingKV" $$ [$Hspkg] as %err ⟨%Herr, -⟩
  · ipureintro
    intro h
    have := go.intoVal_inj h
    simp at this
  (try wp_auto)
  iapply HΦ
  ipureintro
  exact ⟨rfl, Herr⟩

end proof

end leasing
end EtcdGrove
end Perennial
