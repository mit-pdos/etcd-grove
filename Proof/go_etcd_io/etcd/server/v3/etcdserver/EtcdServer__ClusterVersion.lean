/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ClusterVersion.lean`. Lean-first
(no Rocq counterpart); srvBuildGap's rows (2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ClusterVersion

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.ClusterVersion.wp_proof :
    EtcdServer.ClusterVersion.spec (GF := GF) (hG := hG) := by
  intro s cl γcv known
  wp_start as ⟨#Hcl, #Hmono, Hk⟩
  iunfold clusterVersionMono at Hmono
  icases Hmono with ⟨%Hnn, #Hv⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply Hv $$ [Hk] as %v Hr
  · iexact Hk
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
