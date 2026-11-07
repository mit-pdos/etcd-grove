/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__newHeader.lean`. Lean-first (no
Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__newHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreCore


@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.newHeader.wp_proof
    (hID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (hsh : mvcc.api.shapes.law (GF := GF))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG)) :
    EtcdServer.newHeader.spec (GF := GF) (hG := hG) := by
  intro on s E γr cl mid cid
  haveI := Hp.1
  wp_start as ⟨#Hrd, #Hcl, #Hcid, #Hmid, #Hlead, Htt, Hmr⟩
  iunfold isServerReadM at Hrd
  icases Hrd with ⟨%v, #Hf⟩
  iunfold srvReadFieldsAtM at Hf
  icases Hf with ⟨-, -, #HkvA, #Hkv, %Hkveq0, -, -, -, -, -, -, -, #Hterm, -, -, #Hinvs, -⟩
  ihave ⟨#HkS, %Hwit⟩ := srvKVInvsM_kvStoreInv on s E γr $$ Hinvs
  ihave %Hsh := hsh.1 v.kv E.γ $$ Hkv
  obtain ⟨kty, kvv, Hkveq, -, -, hRevC, -⟩ := Hsh
  ihave #Hmem : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_auto
  wp_apply hID cl cid $$ []
  · iframe #
  wp_apply hMID s mid $$ []
  · iframe #
  wp_apply hKV s v.kv $$ []
  · iframe #
  rw [Hkveq]
  wp_auto
  -- `KV().Rev()`: `KV.Rev.contract` at the handle's dynamic type, at the store invariant's read
  -- update from the empty floor
  imod monoListLbOwn_nil (GF := GF) E.γs.slog with #Hc0
  ihave #Hc0' : srvApi.kvLogLb E.γs [] $$ []
  · iunfold srvApi.kvLogLb; iexact Hc0
  haveI := Hwit.1
  haveI := Hwit.2.1
  haveI := Hwit.2.2.1
  haveI := Hwit.2.2.2
  ihave HAU := srvApi.au_read (Nx := E.Nx) (Cp := E.Cp) Hp Hr E.kv E.γ E.γs [] $$ HkS Hc0'
  ihave #Hkv' : mvcc.api.isMvcc (interface.mkOk kty kvv) E.γ $$ []
  · rw [← Hkveq, Hkveq0]; iexact Hkv
  wp_apply (hRevC E.γ (srvApi.kvReadAtG E.Nx E.γs [])) $$ [Htt Hmr HAU]
    as %rev ⟨Htt, Hmr, %σ, Hrd, %Hrev⟩
  · iframe #; iframe Htt Hmr
    iunfold srvApi.auRead at HAU
    iexact HAU
  iunfold srvApi.kvReadAtG at Hrd
  icases Hrd with ⟨-, #Hc, #Hnx, Hrc, %Hσ⟩
  wp_apply hTerm s $$ [] as %t -
  · iframe #
  wp_apply hLead s $$ [] as %l -
  · iframe #
  try wp_auto
  irename «$r0» => Hh
  generalize «$r0_ptr» = h at *
  iapply HΦ
  iframe Htt Hmr
  have hpre := (srvApi.reach_prefix σ Hσ.1).1
  have hlen : 2 ≤ σ.log.length := by
    have := hpre.length_le; simpa [mvcc.api.mvccStart] using this
  have hwf := (mvcc.api.reach_logWf σ Hσ.1).1
  iexists _, σ.log
  iframe Hh Hc Hnx Hrc
  ipureintro
  refine ⟨hwf, by intro h; rw [h] at hlen; simp at hlen, rfl, rfl, ?_⟩
  rw [Hrev, mvcc.api.MvccState.rev]
  show W64 ((σ.log.length - 1 : Nat) : Int) = W64 ((σ.log.length : Int) - 1)
  congr 1
  omega

end proof

end EtcdGrove
end Perennial
