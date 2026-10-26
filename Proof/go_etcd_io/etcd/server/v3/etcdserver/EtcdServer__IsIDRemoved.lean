/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__IsIDRemoved.lean`. Lean-first (no Rocq
counterpart); D21 stage M2 (2026-10-19).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsIDRemoved
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsIDRemoved

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.IsIDRemoved.wp_proof
    (wp_IsIDRemoved : membership.RaftCluster.IsIDRemoved.spec (GF := GF) (hG := hG)) :
    EtcdServer.IsIDRemoved.spec (GF := GF) (hG := hG) := by
  intro γn s id x
  wp_start as #Hok
  iunfold srvProcOk at Hok
  icases Hok with ⟨%l, %c, %st, %γ, #Hlg, %Hlgnn, #Hid, %Hγid, #Hcl, #Hrc, #Hst, %Hstnn, #Hn,
    #Hsi, %HN⟩
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  wp_auto
  wp_apply (membership.RaftCluster.IsIDRemoved.spec_static wp_IsIDRemoved c x)
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
