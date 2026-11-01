/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedRaft__newRaftNode.lean`.
Lean-first (no Rocq counterpart). Its callees with specs: raft's node API's `StartNode`
(`StartNode.spec` in a static cluster, `StartNode.dynamicSpec` in a dynamic one; at the
cluster's storage model, `srvStor`) and `newRaftNode`; Perennial's `sync.Mutex.Lock`/`Unlock` are
its linked results, used directly; the rest are the contracts the spec takes
(`InvNodeStart.lean`). (2026-10-27: over the node API; until then raft's `StartNode.spec`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newRaftNode
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedRaft.newRaftNode.wp_proof
    (wp_StartNode : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      StartNode.spec (GF := GF) (hG := hG))
    (wp_newRaftNode : _root_.Perennial.EtcdGrove.newRaftNode.spec (GF := GF) (hG := hG)) :
    bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG) := by
  intro E γr b ss wal cl dq bv cv lok γs pre pv ps ctxs Q
  letI := srvStor (GF := GF) γr
  intro Hlg Hhb Hvalid Hlok Hstor Hinfl Hdpf Hro Hdccv Hsizes Hasync Happlied
    Hps Hpsne Hnodup H0 Hpslen Hid Hvs
  wp_start as Hpre
  iNamed Hpre
  icases typedPointsto_not_null_dup _ _ _ $$ Hb with ⟨Hb, %Hbnn⟩
  iStructNamedSuffix Hb "B"
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpkgs : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hpkgm : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  (try wp_auto)
  -- `len(b.peers) == 0`: no, the new cluster's path
  ihave %Hlen := ownSlice_len _ _ _ $$ Hpeers
  have Hpvne : pv ≠ [] := by
    intro h; subst h; simp at Hps; exact Hpsne Hps
  have Hlen0 : decide (bv.peers'.len = W64 0) = false := by
    apply decide_eq_false
    intro h
    apply Hpvne
    apply List.eq_nil_of_length_eq_zero
    rw [Hlen.1, h]
    rfl
  rw [Hlen0]
  (try wp_auto)
  -- `raft.StartNode(b.config, b.peers)`: the node API's unified `StartNode`
  wp_apply (wp_StartNode γr γr.cl srvClusterN ps ctxs bv.config' cv lok
      ⟨go.GoType.PointerType MemoryStorage.ty, #bv.storage'⟩
      (HardStateM.mk (W64 0) (W64 0) (W64 0)) memSnapEmpty.Metadata'.ConfState' Q
      bv.peers' dq pv Hvalid Hlok Hstor Hinfl Hdpf Hro Hdccv Hsizes Hasync Happlied
      ⟨rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl Hps) $$ [Hc Hbs Hboot Hpeers]
    as %nd ⟨%n, %Hnd, #Hnode, Hdrv, Hncfg, Hrun, HQ, -⟩
  · iframe #; iframe Hc Hpeers Hboot
    iExactEq Hbs; rfl
  subst Hnd
  (try wp_auto)
  -- `raftStatus = n.Status` under `raftStatusMu`
  iunfold rnRaftStatusOk at Hrs
  wp_apply sync.Mutex.wp_Lock (globalAddr raftStatusMu)
    iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f) $$ [] as ⟨Hlocked, ⟨%f0, Hf⟩⟩
  · iframe #
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock (globalAddr raftStatusMu)
    iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f) $$ [Hlocked Hf]
  · iframe #; iframe Hlocked; inext; iexists _; iexact Hf
  (try wp_auto)
  -- the `isIDRemoved` closure over `cl.IsIDRemoved`
  wp_func_lits
  (try wp_auto)
  ipersist cl
  -- `serverstorage.NewStorage(b.lg, wal, ss)`
  iunfold rnNewStorageOk at Hns
  wp_apply Hns $$ %bv.lg' %wal %ss [] as %st ⟨#Hst, %Hstss⟩
  (try wp_auto)
  -- `newRaftNode(cfg)`
  wp_apply (wp_newRaftNode E γr cv.ID' n pre bv.storage' γs
    (raftNodeConfig.mk bv.lg' _ (interface.mkOk (go.GoType.PointerType node.ty) #n) bv.storage' st
      bv.heartbeat' GoInterface.nil) Hlg Hhb) $$ [] as %r ⟨%γw, %Hγw, Hbuilt⟩
  · iframe #
  (try wp_auto)
  ihave Hb : b ↦{dq} bv $$ [lgB heartbeatB peersB configB storageB]
  · iapply typedPointsto_combine _ _ _ Hbnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  iapply HΦ
  iexists n, γw, _, st
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hγw
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  iframe Hnode Hst Hbuilt Hb HQ Hrun Hncfg
  isplitl [Hdrv]
  · iExactEq Hdrv; rfl
  isplitr
  · -- the closure meets `isRNIDRemoved`
    iunfold isRNIDRemoved
    iintro !> %id' %Φ' !> - HΦ'
    (try wp_auto)
    iunfold rnClusterOk at Hcl
    wp_apply Hcl $$ %id' [] as %bb -
    iapply HΦ'
    first | itrivial | (ipureintro; trivial)
  ipureintro; exact Hstss

end proof

end EtcdGrove
end Perennial
