/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedRaft__newRaftNode.lean`.
Lean-first (no Rocq counterpart). Its callees with specs: raft's `StartNode` (`@`: proved and
linked in raft's `Link.lean`, under raft's `StorageModel`) and `newRaftNode`; Perennial's
`sync.Mutex.Lock`/`Unlock` are its linked results, used directly; the rest are the contracts the
spec takes (`InvNodeStart.lean`).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedRaft.newRaftNode.wp_proof
    (wp_StartNode : StartNode.spec (GF := GF) (hG := hG))
    (wp_newRaftNode : _root_.Perennial.EtcdGrove.newRaftNode.spec (GF := GF) (hG := hG)) :
    bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG) := by
  intro E γ md bud b ss wal cl dq bv cv lok γs reg pre pv ps ctxs bootLog
    Hlg Hhb Hvalid Hlok Hstor Hinfl Hdpf Hro Hdccv Hsizes Hasync Happlied
    Hps Hpsne Hnodup H0 Hpslen Hid Hcfg Hboot HbootOk _
  wp_start as Hpre
  iNamed Hpre
  rw [method_unfold (t := go.GoType.PointerType bootstrappedRaft.ty) (m := go!"newRaftNode")]
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
  -- `raft.StartNode(b.config, b.peers)`, in the mode `md` (2026-10-25, T-M M2a: `bootInit`; D43 M3)
  wp_apply (wp_StartNode γ md bud bv.config' cv lok ⟨go.GoType.PointerType MemoryStorage.ty, #bv.storage'⟩
    memStorEmpty (HardStateM.mk (W64 0) (W64 0) (W64 0)) (ConfStateM.mk [] [] [] [] false)
    (memSnapTok bv.storage' γs memStorEmpty) bv.peers' dq pv ps ctxs bootLog false Hvalid Hlok Hstor Hinfl Hdpf Hro Hdccv Hsizes Hasync
    Happlied rfl rfl (Or.inr rfl) rfl ⟨rfl, rfl, rfl⟩ rfl rfl rfl rfl
    rfl Hps Hpsne Hnodup H0 Hpslen Hid Hcfg Hboot HbootOk rfl (fun h => by cases h))
    $$ [Hc Hsto Hghost Hpeers Htok] as %nd ⟨Htok, Hpost⟩
  · rw [show (GoInterface.ok (⟨go.GoType.PointerType MemoryStorage.ty, #bv.storage'⟩ : GoInterfaceOk)) =
      memStorIface bv.storage' from rfl]
    rw [show (⟨go.GoType.PointerType MemoryStorage.ty, #bv.storage'⟩ : GoInterfaceOk).ty =
      go.GoType.PointerType MemoryStorage.ty from rfl]
    rw [show (⟨go.GoType.PointerType MemoryStorage.ty, #bv.storage'⟩ : GoInterfaceOk).v =
      #bv.storage' from rfl]
    rw [method_unfold (t := go.GoType.PointerType MemoryStorage.ty) (m := go!"InitialState")]
    iframe #; iframe Hc Hsto Hghost Hpeers
    -- (D17d) `InitialState` borrows the snapshot token
    iintro %Φ %ss' Hs HK
    iapply Hinit $$ Hs Htok
    iintro %hp %cs %al Hs Ht Hhs Hcs
    iapply HK $$ Hs Ht Hhs Hcs
  icases Hpost with ⟨%γn, %n, %Hnd, %Hmd, #Hnode, Hdrv, Hncfg, Hpeers⟩
  obtain ⟨Hγraft, Hγbud, Hγstor, Hγmode, -, Hndeq⟩ := Hnd
  subst Hndeq
  (try wp_auto)
  -- `raftStatus = n.Status` under `raftStatusMu`
  iunfold rnRaftStatusOk at Hrs
  wp_apply sync.Mutex.wp_Lock (globalAddr raftStatusMu) iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f)
    $$ [] as ⟨Hlocked, ⟨%f0, Hf⟩⟩
  · iframe #
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock (globalAddr raftStatusMu) iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f)
    $$ [Hlocked Hf]
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
  wp_apply (wp_newRaftNode E γn cv.ID' n pre bv.storage' γs reg
    (raftNodeConfig.mk bv.lg' _ (interface.mkOk (go.GoType.PointerType node.ty) #n) bv.storage' st
      bv.heartbeat' GoInterface.nil) Hlg Hhb) $$ [] as %r ⟨%γw, %Hγw, Hbuilt⟩
  · iframe #
  (try wp_auto)
  ihave Hb : b ↦{dq} bv $$ [lgB heartbeatB peersB configB storageB]
  · iapply typedPointsto_combine _ _ _ Hbnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  iapply HΦ
  iexists γn, n, γw, _, st
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Hγw
    exact ⟨Hγraft, Hγbud, Hγstor, Hγmode, Hmd, h1, h2, h3, h4, h5,
      h6, h7⟩
  iframe Hnode Hdrv Hncfg Hst Hbuilt Hb Hpeers Htok
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
