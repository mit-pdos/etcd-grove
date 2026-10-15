/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__FeatureEnabled.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FeatureEnabled

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.FeatureEnabled.wp_proof :
    EtcdServer.FeatureEnabled.spec (GF := GF) (hG := hG) := by
  intro s fg f
  wp_start as ⟨#Hfg, #Hgate⟩
  iunfold isFeatureGate at Hgate
  icases Hgate with ⟨%fi, %Hfi, #HEn⟩
  wp_auto
  subst Hfi
  wp_auto
  wp_apply HEn as %b -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
