/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__CutPeer.lean`. Lean-first (no Rocq
counterpart); the partition plan's stage S2 (2026-10-20). The type assertion on `s.r.transport`
succeeds: `srvNetMember` says the field holds the started `*rafthttp.Transport` `t`
(`transportIface t`), on which the transport's axiom applies.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__CutPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__CutPeer

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

theorem EtcdServer.CutPeer.wp_proof
    (wp_CutPeer : rafthttp.Transport.CutPeer.spec (GF := GF) (hG := hG)) :
    EtcdServer.CutPeer.spec (GF := GF) (hG := hG) := by
  intro γn s mid id
  wp_start as #Hm
  iunfold srvNetMember at Hm
  icases Hm with ⟨-, %t, #Htr, #Hts, #Hrem⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_CutPeer γn t id [])
  · iframe #
    ipureintro; simp
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
