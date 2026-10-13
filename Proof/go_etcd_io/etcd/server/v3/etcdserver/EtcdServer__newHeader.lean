/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__newHeader.lean`. Lean-first (no
Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__newHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

theorem EtcdServer.newHeader.wp_proof
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG)) :
    EtcdServer.newHeader.spec (GF := GF) (hG := hG) := by
  have hRev := mvcc.store.Rev.spec_frozen hRev
  intro s E γr cl mid
  wp_start as ⟨#Hrd, #Hcl, #Hmid, #Hlead, Hsr⟩
  iunfold isServerRead at Hrd
  icases Hrd with ⟨%v, #Hf⟩
  iunfold srvReadFieldsAt at Hf
  icases Hf with ⟨-, -, #HkvA, #Hkv, #HrvA, #Hrv, -, -, -, -, -, -, -, #Hterm, -, -⟩
  iunfold txn.isKV at Hkv
  icases Hkv with ⟨%Hkv, #Hs⟩
  ihave #Hmem : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_auto
  wp_apply hID cl $$ [] as %cid -
  wp_apply hMID s mid $$ []
  · iframe #
  wp_apply hKV s v.kv $$ []
  · iframe #
  rw [Hkv]
  wp_auto
  imod ownToks_0 (GF := GF) E.γ.revs with Hnone
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #Hc0
  wp_apply hRev E.s v.rv E.γ 0 [] $$ [Hsr Hnone] as %rev ⟨Hsr, -, %log, #Hc, %Hl⟩
  · iframe #; iframe
  wp_apply hTerm s $$ [] as %t -
  · iframe #
  wp_apply hLead s $$ [] as %l -
  · iframe #
  try wp_auto
  wp_alloc h as Hh
  wp_auto
  iapply HΦ
  iframe Hsr
  iexists _, log
  iframe Hh Hc
  ipureintro
  exact ⟨Hl.2.2.1, rfl, Hl.2.2.2⟩

end proof

end EtcdGrove
end Perennial
