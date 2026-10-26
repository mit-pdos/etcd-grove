/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__MendPeer.lean`. Lean-first (no Rocq
counterpart); the partition plan's stage S2 (2026-10-20). The type assertion on `s.r.transport`
succeeds: `srvNetMember` says the field holds the frozen `*rafthttp.Transport` `τ.t`
(`transportIface τ.t`), on which the transport's spec applies (with a reader's token, 2026-10-24).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MendPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__MendPeer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.MendPeer.wp_proof
    (wp_MendPeer : rafthttp.Transport.MendPeer.spec (GF := GF) (hG := hG)) :
    EtcdServer.MendPeer.spec (GF := GF) (hG := hG) := by
  intro hpp γn s mid id τ
  wp_start as ⟨#Hm, Htok⟩
  iunfold srvNetMember at Hm
  icases Hm with ⟨-, #Htr, %Hlid, %rs, #Hf, %Hrs⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
  · iPkgInit
  wp_auto
  iunfold srvTrTok at Htok
  wp_apply (wp_MendPeer hpp γn τ.t τ.c rs id (by rw [Hrs.1]; simp)) $$ [Htok] as Htok
  · iframe; iframe #
  iapply HΦ
  iunfold srvTrTok
  iexact Htok

end proof

end EtcdGrove
end Perennial
