/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedRaft__newRaftNode.lean`.
Lean-first (no Rocq counterpart). Its callees with specs: raft's node API's `StartNode`
(`StartNode.spec`, at the cluster's storage model, `srvStor`) and `newRaftNode`; Perennial's `sync.Mutex.Lock`/`Unlock` are
its linked results, used directly; `NewStorage`'s contract is a law (`rnNewStorageOk.law`, wal-nostorageok,
2026-11-21); the rest are the contracts the spec takes (`InvNodeStart.lean`). (2026-10-27: over the node API; until then raft's `StartNode.spec`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newRaftNode
public import Perennial.Proof.sync
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrashSteps

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
    (wp_RestartNode : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      RestartNode.spec (GF := GF) (hG := hG))
    (wp_newRaftNode : _root_.Perennial.EtcdGrove.newRaftNode.spec (GF := GF) (hG := hG))
    -- (wal-nostorageok, 2026-11-21: until then the spec's premise `rnNewStorageOk`) `NewStorage`'s contract,
    -- proved over the real WAL (`rnNewStorageOk_law_holds`)
    (hNewStorage : rnNewStorageOk.law (GF := GF) (hG := hG))
    -- (P5, 2026-11-25) the crash-aware durability's allocation at a restart (isolated: the restart slot's
    -- restatement is pending, #50)
    (hRestartAlloc : rnRestartAllocK.law (GF := GF)) :
    bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG) := by
  intro E γr b ss wal cl sd dq bv cv lok γs pre hw pv ps ctxs Q bt
  letI := srvStor (GF := GF) γr
  intro SV hPers hValid
  wp_start as Hpre
  iNamed Hpre
  obtain ⟨Hhb, HwalW, HtrC⟩ := Hraft
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
  ihave %Hlen := ownSlice_len _ _ _ $$ Hpeers
  -- (restart S3 item 5) `len(b.peers) == 0`: `RestartNode` at a restart, `StartNode` fresh; joined
  -- at the node `nn`, its key `K` and what the start gives of the boot
  wp_join iprop(∃ (nn : NodeH) (K : GName) (view : GoSlice),
      terms_ptr ↦ view ∗ view ↦*□ bt.seedRuns ∗
      n_ptr ↦ interface.mkOk (go.GoType.PointerType node.ty) #nn.loc ∗ b_ptr ↦ b ∗
      b.[bootstrappedRaft, go!"config"] ↦{dq} bv.config' ∗ b.[bootstrappedRaft, go!"storage"] ↦{dq} bv.storage' ∗
      b.[bootstrappedRaft, go!"peers"] ↦{dq} bv.peers' ∗ bv.peers' ↦*{dq} pv ∗
      isNode nn γr.cl srvClusterN cv.ID' ∗ nodeRunning nn γr.cl srvClusterN 1 ∗ nodeTagPin γr.cl nn SV ∗
      rnBootPost γr nn K bv cv ps ctxs bt ∗ Q K ∗
      -- (P5) the crash-aware durability, allocated once the node is started
      ∃ νk : WalNamesK GF, ⌜νk.ν.h = hw ∧ νk.sd = (fun _ => iprop(True))⌝ ∗
        rnDurInvK γr cv.ID' νk hw ∗ nodeArm nn γr.cl νk.x ∗ rnWalViewK νk (bt.view γr, none) ∗
        token νk.ν.stop ∗ token νk.ν.app ∗ walCommitLb νk.ν (bt.view γr).l)
    at next with [n terms b configB peersB storageB Hc Hpeers Hboot Hwal] as ⟨%nn, %K, %view, terms, #Hseed, n, b, configB, storageB, peersB, Hpeers,
      #Hnode, Hrun, #Hpin, Hbpost, HQ, %νk, %Hνk, #Hdur, #Harm, Hwv, Hwst, Hwap, #Hwlb⟩
  · cases bt with
    | fresh =>
      iunfold rnBootPre at Hboot
      icases Hboot with ⟨%Hcfg, Hbs, Hboot, Hvac, Hrst⟩
      -- (2026-11-21, the crash invariant) the vacancy armed (the server keeps no crash token: its
      -- restart follows `node.Stop`)
      imod nodeVacant_armD γr.cl cv.ID' ⊤ $$ Hvac with ⟨%x, Hvac⟩
      have Hpvne : pv ≠ [] := by
        intro h; have := Hcfg.peers; subst h; simp at this; exact Hcfg.peersNe this
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
      ihave Hau : AU <{ ∃∃ (S : RaftState), raftState γr.cl cv.ID' S ∗ ⌜S = RaftState.init⌝ }>
          @ ⊤ \ ↑srvClusterN, ∅
          <{ raftState γr.cl cv.ID' S, COMM raftState γr.cl cv.ID' RaftState.init }> $$ [Hrst]
      · iauintro
        unfold atomic_acc
        iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑srvClusterN from
          Std.LawfulSet.empty_subset)
        iintro Hclose
        isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
        iexists RaftState.init
        iframe Hrst
        isplitr
        · ipureintro; rfl
        isplit
        · iintro ⟨H, -⟩
          imod Hclose with -
          imodintro
          iexact H
        · iintro H
          imod Hclose with -
          imodintro
          iexact H
      iapply wp_fupd
      wp_apply (wp_StartNode γr γr.cl srvClusterN ps ctxs bv.config' cv lok
          ⟨go.GoType.PointerType MemoryStorage.ty, #bv.storage'⟩
          memSnapEmpty.Metadata'.ConfState' (raftState γr.cl cv.ID' RaftState.init) Q
          bv.peers' dq pv SV hValid Hcfg.valid Hcfg.logger Hcfg.storage Hcfg.inflight Hcfg.noForwarding
          Hcfg.readOnly Hcfg.ccValidation Hcfg.sizes Hcfg.noAsync (fun _ => Hcfg.maxMsg) Hcfg.applied
          rfl rfl rfl rfl rfl Hcfg.peers Hcfg.traceLogger HtrC x) $$ [Hc Hbs Hboot Hvac Hau Hpeers]
        as %nd ⟨%n', %K, %Hnd, #Hfresh, #Hnode, Hdrv, Hncfg, Hrun, #Hpin, #Harm, Hrst, HQ, Hpeers⟩
      · iframe #; iframe Hc Hpeers Hboot Hvac Hau
        iExactEq Hbs; rfl
      subst Hnd
      -- (P5) the crash-aware durability over the fresh records, at raft's initial state
      iunfold rnBootWal at Hwal
      imod rnDurK_alloc_fresh γr cv.ID' x (fun _ => iprop(True)) hw $$ Hwal Hrst
        with ⟨%νk, %Hνk, #Hdur, Hwv, Hwst, Hwap, #Hwlb⟩
      imodintro
      (try wp_auto)
      isplitr
      · itrivial
      iexists n', K, slice.nil
      ihave #Hseed := ownSlice_nil (GF := GF) (V := replayTermRun) DFrac.discard
      simp only [RNBoot.seedRuns]
      iframe terms Hseed n b configB storageB peersB Hpeers Hnode Hrun Hpin HQ
      isplitl [Hdrv Hncfg]
      · simp only [rnBootPost]
        iframe Hfresh Hncfg
        iExactEq Hdrv; rfl
      iexists νk
      simp only [RNBoot.view]
      iframe Hdur Hwv Hwst Hwap Hwlb
      isplitr
      · ipureintro; exact ⟨Hνk.2.2, Hνk.2.1⟩
      rw [Hνk.1]; iexact Harm
    | restart σ cs S a m A₀ =>
      iunfold rnBootPre at Hboot
      icases Hboot with ⟨%Hpure, Hbs, #Hclu, #Hfits, ⟨%x, Hvac⟩, Hrst, #Hconf⟩
      obtain ⟨Hcfg, Hba, Hac, Hboot, Hcs, Hhold, Hnsm⟩ := Hpure
      have Hlen0 : decide (bv.peers'.len = W64 0) = true := by
        apply decide_eq_true
        have h1 := Hlen.1
        rw [Hcfg.peersNil] at h1
        simp at h1
        word
      rw [Hlen0]
      (try wp_auto)
      wp_bind (App (Val (@! replayTermsFromStorage)) (Val #bv.storage'))
      iapply Hbs
      inext
      iintro %out ⟨#Hseed, Hbs⟩
      (try wp_auto)
      -- `raft.RestartNode(b.config)`: the update checks that the storage holds `S` (under a later:
      -- `raftState` is not timeless)
      ihave Hrst : ▷ raftState γr.cl cv.ID' S $$ [Hrst]
      · imodintro; iexact Hrst
      ihave Hau : AU <{ ∃∃ (S' : RaftState), ▷ raftState γr.cl cv.ID' S' ∗ ⌜StorageHolds S' σ⌝ }>
          @ ⊤ \ ↑srvClusterN, ∅
          <{ raftState γr.cl cv.ID' S',
            COMM (fun S'' => iprop(raftState γr.cl cv.ID' S'' ∗ ⌜S'' = S⌝)) S' }> $$ [Hrst]
      · iauintro
        unfold atomic_acc
        iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑srvClusterN from
          Std.LawfulSet.empty_subset)
        iintro Hclose
        isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
        iexists S
        isplitl [Hrst]
        · isplitl [Hrst]
          · iexact Hrst
          · ipureintro; exact Hhold
        isplit
        · iintro ⟨H, -⟩
          imod Hclose with -
          imodintro
          iexact H
        · iintro H
          imod Hclose with -
          imodintro
          iframe H
          ipureintro; rfl
      -- (2026-11-22) the update with the crash token (`restartAu_nc`)
      ihave Hau := restartAu_nc _ _ _ _ _ $$ Hau
      iapply wp_fupd
      wp_apply (wp_RestartNode γr γr.cl srvClusterN bv.config' cv lok
          ⟨go.GoType.PointerType MemoryStorage.ty, #bv.storage'⟩ σ cs a m
          (fun S'' => iprop(raftState γr.cl cv.ID' S'' ∗ ⌜S'' = S⌝)) Q
          SV hValid Hcfg.valid Hcfg.logger Hcfg.storage Hcfg.inflight Hcfg.noForwarding
          Hcfg.readOnly Hcfg.ccValidation Hcfg.sizes Hcfg.noAsync (fun _ => Hcfg.maxMsg)
          (Or.inl (by rw [Hcfg.applied]; rfl)) (by rw [Hcfg.applied]; simpa using Hba) Hac Hboot Hcs Hnsm
          Hcfg.traceLogger HtrC x)
        $$ [Hc Hbs Hvac Hau]
        as %nd ⟨%n', %S', %l, %K, %Hnd, #Hnode, #Hl, %Hll, %-, Hdrv, Hncfg, Hrun, #Hpin, #Harm, #Hst0, Hrst, HQ⟩
      · iframe #; iframe Hc Hvac Hau
        rw [Hcfg.applied]
        iExactEq Hbs; rfl
      subst Hnd
      -- (P5) the crash-aware durability at the restart's view (the isolated restart step)
      icases Hrst with ⟨Hrst, %HSS⟩
      subst HSS
      iunfold rnBootWal at Hwal
      icases Hwal with ⟨Hwr, %Hvw, #Hwc, #Hwl0⟩
      imod hRestartAlloc γr cv.ID' x (fun _ => iprop(True)) hw σ S' _ Hvw $$ Hwr Hwc Hwl0 Hrst
        with ⟨%νk, %Hνk, #Hdur, Hwv, Hwst, Hwap, #Hwlb⟩
      imodintro
      (try wp_auto)
      isplitr
      · itrivial
      iexists n', K, out
      simp only [RNBoot.seedRuns]
      iframe terms Hseed n b configB storageB peersB Hpeers Hnode Hrun Hpin HQ
      isplitl [Hdrv Hncfg]
      · simp only [rnBootPost]
        iexists l
        iframe Hl Hncfg Hst0
        isplitr
        · ipureintro; rw [Hll, Hcfg.applied]; simp
        iExactEq Hdrv; rfl
      iexists νk
      simp only [RNBoot.view]
      iframe Hdur Hwv Hwst Hwap Hwlb
      isplitr
      · ipureintro; exact ⟨Hνk.2.2, Hνk.2.1⟩
      rw [Hνk.1]; iexact Harm
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
  ihave #Hns := hNewStorage $$ Hpkgs
  iunfold rnNewStorageOk at Hns
  subst HwalW
  wp_apply Hns $$ %bv.lg' %ss %sd %hw [] as %st ⟨#Hst, Hrd1, Hrd2⟩
  · iexact Hssi
  (try wp_auto)
  -- `newRaftNode(cfg)`
  wp_apply (wp_newRaftNode E γr cv.ID' nn pre bv.storage' γs K νk ss
    (raftNodeConfig.mk view bv.lg' _ (interface.mkOk (go.GoType.PointerType node.ty) #nn.loc) bv.storage' st
      bv.heartbeat' GoInterface.nil) bt.a0 bt.t0 bt.P bt.commit0 bt.snap0) $$ []
    as %r ⟨%γw, %Hγw, Hbuilt⟩
  · iframe #
    ipureintro; exact ⟨Hhb, bt.P_prefix⟩
  (try wp_auto)
  ihave Hb : b ↦{dq} bv $$ [lgB heartbeatB peersB configB storageB]
  · iapply typedPointsto_combine _ _ _ Hbnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  iapply HΦ
  iexists nn, γw, _, st, view
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, h8', h9, h10⟩ := Hγw
    refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, h8', h9, h10⟩
    · simp only [RNNames.wal, h8]; exact Hνk.1
    · rw [h8]; exact Hνk.2
  obtain ⟨-, -, -, -, -, -, hkey, hwal, hss, -⟩ := Hγw
  subst hkey
  have hwh : γw.wal.h = hw := by simp only [RNNames.wal, hwal]; exact Hνk.1
  ihave #Hst' : isWalStorage st γw.wal.h γw.ss $$ []
  · rw [hwh, hss]; iexact Hst
  ihave Hrd1' : walStorRd st γw.wal.h $$ [Hrd1]
  · rw [hwh]; iexact Hrd1
  ihave Hrd2' : walStorRd st γw.wal.h $$ [Hrd2]
  · rw [hwh]; iexact Hrd2
  -- (P5) the crash-aware durability at the wrapper's names
  ihave #Hdur' : rnDurInvK γr cv.ID' γw.walK hw $$ []
  · rw [hwal]; iexact Hdur
  ihave #Harm' : nodeArm nn γr.cl γw.walK.x $$ []
  · rw [hwal]; iexact Harm
  ihave Hwv' : rnWalViewK γw.walK (bt.view γr, none) $$ [Hwv]
  · rw [hwal]; iexact Hwv
  ihave Hwtok : token γw.wal.stop ∗ token γw.wal.app ∗ walCommitLb γw.wal (bt.view γr).l $$ [Hwst Hwap]
  · simp only [RNNames.wal]; rw [hwal]; iframe Hwst Hwap Hwlb
  icases Hwtok with ⟨Hwst', Hwap', #Hwlb'⟩
  iframe Hseed Hnode Hst' Hrd1' Hrd2' Hbuilt Hb Hpeers HQ Hrun Hpin Hbpost Hdur' Harm' Hwv' Hwst' Hwap' Hwlb'
  -- the closure meets `isRNIDRemoved`
  iunfold isRNIDRemoved
  iintro !> %id' %Φ' !> - HΦ'
  (try wp_auto)
  iunfold rnClusterOk at Hcl
  wp_apply Hcl $$ %id' [] as %bb -
  iapply HΦ'
  first | itrivial | (ipureintro; trivial)

end proof

end EtcdGrove
end Perennial
