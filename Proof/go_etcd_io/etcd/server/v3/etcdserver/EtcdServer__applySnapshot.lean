/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13): no snapshot. D22 receiver epochs, S8d
(2026-10-26): a non-empty snapshot, `applySnapshot_walk` (`SnapApplyWalk.lean`) and
`srvSnapApplied_of_walk` (`SnapApplyPost.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyWalk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyPost
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Recover

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem EtcdServer.applySnapshot.wp_proofEmpty
    (hIES : IsEmptySnap.spec (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.specEmpty (GF := GF) (hG := hG) := by
  intro s ep ap
  wp_start as #Hsn
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_IsEmptySnap_nil hIES) $$ [$Hrpkg]
  (try wp_auto)
  iapply HΦ
  itrivial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`applySnapshot` with a non-empty snapshot, in the server's auth mode** (F9; P6.2, 2026-11-03):
`specSnapM`, from its callees' specs and the auth store's `Recover` (used with auth on, through
`authRecoverOn_glue`): the mode-generic walk (`applySnapshot_walk`) and post
(`srvSnapApplied_of_walk`), then `srvSnapAppliedM` by the mode (`srvSnapAppliedM_of_G`). -/
theorem EtcdServer.applySnapshot.wp_proof_snapM
    (hIES : IsEmptySnap.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (hOSB : storage.OpenSnapshotBackend.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hBUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hSB : consistentIndex.SetBackend.spec (GF := GF) (hG := hG))
    (hLR : lease.lessor.Recover.spec (GF := GF) (hG := hG))
    (hRst : mvcc.watchableStore.Restore.spec (GF := GF) (hG := hG))
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hGTP : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hSTP : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hRel : storage.storage.Release.spec (GF := GF) (hG := hG))
    (hNAB : schema.NewAlarmBackend.spec (GF := GF) (hG := hG))
    (hAR : v3alarm.AlarmStore.Recover.spec (GF := GF) (hG := hG))
    (hNAuB : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    (hNMB : schema.NewMembershipBackend.spec (GF := GF) (hG := hG))
    (hCSB : membership.RaftCluster.SetBackend.spec (GF := GF) (hG := hG))
    (hClose : backend.backend.Close.spec (GF := GF) (hG := hG))
    (hCRec : membership.RaftCluster.Recover.spec (GF := GF) (hG := hG))
    (hRAP : rafthttp.Transport.RemoveAllPeers.spec (GF := GF) (hG := hG))
    (hAP : rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hNUA : EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG))
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hRec : auth.authStore.Recover.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.specSnapM (GF := GF) (hG := hG) := by
  · intro s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmmap tI hmeta st b hle al ast lp cl x A hRO hwq R hpre hRok r hcc hkI hbr hlp γp hrbw stp γd γt img nt hstp hnt halarm halbi hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad hbuq A' hAA' hA' hleaseI hlnil hpre0 hlmk hany hauthI γnc
    iintro %Φ Hpre HΦ
    icases Hpre with ⟨#Hpkg, #Hsrv, #Hsn, #Hsnap, #Hnc, #Hncb, Hrcv, Hai, Hat, Hdsi, Hlr, Hbr, Htk, #Hcfg, #Hssf, #Hhkf, #Hiss, Hfile, Hpath, #Hfg, #Hbh, Hst, Hab, HKV, HRS, #HAlb, #Hlinv, #Hlpf, #Hlrev, Hkvc, #Hkvex, #Hcok, #Hrcpt, #Hpf, #Hpc, #HkSz, #HWP, #Hstpf, #Hsdinv, Hγt, #Half, #HisAl, #Haustf, #Hclf, #Hirc, #Htrf, Htlive, #Hmidf, #Hmembers, Hmsi, Hcs0, #Hfgf, #Hfgok, #Hqbf, #Hwadf, #HoSC, HoOh, HauR, #HalA, #HauA, #HleA, #HclA, #Hlcfg, #Hllk, #Hrcn, #HmetaB⟩
    -- (the lease-expiry plan's S2–S4, 2026-11-05) a cluster that grants leases restores the image's
    -- records (`Recover` at the lessor's mode, the records `imageLeasesAt_recs`)
    cases hlgE : E.lg
    case true =>
      -- the KV invariant: auth off (with auth on a cluster grants no lease, `srvKVInvsM_lg`)
      ihave #Hsrv3 := Hsrv
      iunfold isServerM at Hsrv3
      icases Hsrv3 with ⟨-, -, -, #Hat3, -, -, -⟩
      iunfold srvAtomicsM at Hat3
      icases Hat3 with ⟨-, -, #HkM⟩
      ihave %Hon := srvKVInvsM_lg _ _ _ _ $$ HkM
      have hklg : γr.kv.lg = true := by
        rw [KVNames.lg_eq, ← hlmk, ← apply.AEnv.lg_eq]; exact hlgE
      have hon : E.authOn = false := by
        cases hao : E.authOn
        · rfl
        · rw [Hon hao] at hklg; cases hklg
      have ekv : srvKVInvsM (GF := GF) E.authOn s E γr = srvKVInvs E γr := by rw [hon]; rfl
      ihave #HkO : srvKVInvs E γr $$ []
      · rw [← ekv]; iexact HkM
      iunfold srvKVInvs at HkO
      icases HkO with ⟨#HkI, -, #HrI, -⟩
      imod kv_log_plain γr.raft γr.kv A' $$ HkI HrI HAlb with %Hpl0
      imod kv_grantLog_nodup γr.raft γr.kv A' $$ HkI HrI HAlb with %Hnd
      -- the apply thread's rest buckets, opened
      ihave ⟨%f0, %Hf0, HRO, HL0, #HGI, #HRq, HEv⟩ := srvRest_open E γr A $$ HRS
      ihave ⟨%U, HEvU, %HUok⟩ := srvEver_open E A $$ HEv
      have hsI : ∀ X : List w64, srvIds E X = X := fun X => by simp [srvIds, hlgE]
      have eG : srvGrantIf (GF := GF) E = srvGrantable E := by
        unfold srvGrantIf; rw [hlgE]; rfl
      have eQ : srvReqsIf (GF := GF) E (appliedTable γr A) = srvReqs E (appliedTable γr A) := by
        unfold srvReqsIf; rw [hlgE]; rfl
      ihave #HGr : srvGrantable E $$ []
      · rw [← eG]; iexact HGI
      ihave #HRq2 : srvReqs E (appliedTable γr A) $$ []
      · rw [← eQ]; iexact HRq
      iunfold srvGrantable at HGr
      icases HGr with ⟨#HGall, -⟩
      iunfold srvReqs at HRq2
      -- the image's records (`imageLeasesAt_recs`) and their TTLs
      obtain ⟨recs, hbe, hperm', -, hge⟩ := imageLeasesAt_recs hleaseI
      obtain ⟨f, hfT, hfb⟩ := hleaseI
      have hnT' : (appliedTable γr A').ids.Nodup := appliedTable_nodup γr A'
      have hmodes : E.lm = .mono ∨ E.lm = .revocable := by
        have hc := hlgE
        rw [apply.AEnv.lg_eq] at hc
        revert hc
        cases E.lm
        · intro hc; simp at hc
        · intro _; exact Or.inl rfl
        · intro _; exact Or.inr rfl
      have hpl : E.lm = .mono → plainLogM γr.kv.cmp .mono A' := fun h => by
        have := Hpl0.1; rw [← hlmk, h] at this; exact this
      have hnd' : E.lm = .revocable → (srvGrantLog A').Nodup := fun h => Hnd (by rw [← hlmk]; exact h)
      -- (S2, F7) a record whose id the lessor had is the applied table's lease, its request the table's
      have hUq : (decide (E.lm = .mono) = true → ∀ u ∈ U, u ∈ srvIds E (appliedTable γr A).ids) →
          ∀ x ∈ recs, x.1 ∈ U → ∃ q ∈ appliedTable γr A, q.1 = x.1 ∧
            q.2 = tableReq (appliedTable γr A') x.1 := by
        intro hmU x hx hxU
        have hxT' : x.1 ∈ (appliedTable γr A').ids := hperm'.mem_iff.1 (List.mem_map.2 ⟨x, hx, rfl⟩)
        obtain ⟨q, hq, hq1⟩ := List.mem_map.1 hxT'
        refine ⟨q, ?_, hq1, ?_⟩
        · rcases hmodes with hm | hm
          · have hxT : x.1 ∈ (appliedTable γr A).ids := by
              have := hmU (by simp [hm]) x.1 hxU; rwa [hsI] at this
            obtain ⟨q0, hq0, hq01⟩ := List.mem_map.1 hxT
            have hq0' := appliedTable_mono_mem γr hAA' (hpl hm) q0 hq0
            have heq := table_eq_of_id hnT' hq0' hq (hq01.trans hq1.symm)
            rw [← heq]; exact hq0
          · exact appliedTable_rev_mem γr hAA' (hnd' hm) q
              (by rw [hq1]; exact HUok.2 hm x.1 hxU) hq
        · rw [← hq1, tableReq_of_mem hnT' hq]
      have hrmono : decide (E.lm = .mono) = true →
          ∀ id ∈ srvIds E (appliedTable γr A).ids, id ∈ recs.map (·.1) := by
        intro hm id hid
        rw [hsI] at hid
        exact hperm'.mem_iff.2 (appliedTable_mono_sub γr hAA' (hpl (of_decide_eq_true hm)) id hid)
      have hrUL : decide (E.lm = .mono) = false →
          ∀ id ∈ recs.map (·.1), id ∈ U → id ∈ srvIds E (appliedTable γr A).ids := by
        intro hm id hid hU
        rw [hsI]
        have hr : E.lm = .revocable := by
          rcases hmodes with h | h
          · simp [h] at hm
          · exact h
        exact appliedTable_granted_live γr hAA' (hnd' hr) id (HUok.2 hr id hU) (hperm'.mem_iff.1 hid)
      have hreq : ∀ x ∈ recs, sint.Z (tableReq (appliedTable γr A') x.1) ≤ sint.Z x.2.1 := by
        intro x hx
        obtain ⟨q, hq, hq1⟩ := List.mem_map.1 (hperm'.mem_iff.1 (List.mem_map.2 ⟨x, hx, rfl⟩))
        rw [← hq1, tableReq_of_mem hnT' hq]
        exact hge x hx q hq hq1
      have hperm : (srvIds E (appliedTable γr A').ids).Perm (recs.map (·.1)) := by
        rw [hsI]; exact hperm'.symm
      -- the walk's lessor premises
      ihave #HRqs : □ (⌜decide (E.lm = .mono) = true → ∀ u ∈ U, u ∈ srvIds E (appliedTable γr A).ids⌝ -∗
          [∗list] x ∈ recs, ⌜x.1 ∉ U⌝ ∨
            lease.leaseReqIs E.γ.leases x.1 (tableReq (appliedTable γr A') x.1)) $$ []
      · iintro !> %hmU
        have key : □ (∀ p : w64 × w64, ⌜p ∈ appliedTable γr A⌝ -∗
            lease.leaseReqIs E.γ.leases p.1 p.2) ⊢
            [∗list] x ∈ recs, (⌜x.1 ∉ U⌝ ∨
              lease.leaseReqIs (GF := GF) E.γ.leases x.1 (tableReq (appliedTable γr A') x.1)) := by
          apply BigSepL.bigSepL_intro
          intro k x hk
          refine intuitionistically_elim.trans ?_
          iintro #H
          by_cases hxU : x.1 ∈ U
          · obtain ⟨q, hq, hq1, hq2⟩ := hUq hmU x (List.mem_of_getElem? hk) hxU
            iright
            rw [← hq2, ← hq1]
            iapply H; ipureintro; exact hq
          · ileft; ipureintro; exact hxU
        iapply key
        iexact HRq2
      ihave #HGrs : □ ([∗list] id ∈ recs.map (·.1), lease.leaseGranted E.γ.leases id) $$ []
      · iintro !>
        have key : □ (∀ id : w64, lease.leaseGranted (GF := GF) E.γ.leases id) ⊢
            [∗list] id ∈ recs.map (·.1), lease.leaseGranted E.γ.leases id := by
          apply BigSepL.bigSepL_intro
          intro k x hk
          refine intuitionistically_elim.trans ?_
          iintro #H; iapply H
        iapply key; iexact HGall
      iapply wp_fupd
      iapply (applySnapshot_walk hIES hLg hInfo hU64 hGI hGT hOSB hOn hSave hPut hBUR hID hName hSafe s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmmap tI hmeta hSB st b hle hLR al ast lp cl x A hRO hany (fun _ => authRecoverOn_glue hRec) (decide (E.lm = .mono)) recs U
        (tableReq (appliedTable γr A')) (srvIds E (appliedTable γr A').ids)
        (srvIds E (appliedTable γr A).ids) hbe hrmono hrUL (fun _ => hlgE) hreq hperm
        (fun h => by rw [hlgE] at h; cases h)
        (apply.restLeasesWith f0 (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) hwq hRst hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL hCB hDel R hpre hRok r hcc hkI hbr hGTP hSTP hCIg γp hrbw hRel stp γd γt img nt hstp hnt hNAB hAR halarm halbi hlp hNAuB A' hauthI hNMB hCSB hmemb hClose hCRec memI himg hRAP hAP hMID γn t c rs dir ps idm hdir hdok hps hlid hNUA msi cs0 fg quota wad hbuq γnc hAG hLSR hUSR hWrite hTODO) $$ [Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRO HL0 HEvU Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR]
      · iframe #
        iframe Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRO HL0 HEvU Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR
      iintro !> ⟨Hw, Hrcv, Htk⟩
      have hUok' : srvEverOk E A' (U ++ recs.map (·.1)) := by
        refine ⟨fun h => (by rw [hlgE] at h; cases h), fun hr u hu => ?_⟩
        rcases List.mem_append.1 hu with h | h
        · exact srvGrantLog_prefix hAA' u (HUok.2 hr u h)
        · exact appliedTable_ids_granted γr hpre0 A' u (hperm'.mem_iff.1 h)
      have hbkG := snap_bkG E.authMode γr d.P D A' hany hA'.1 f (srvIds E (appliedTable γr A').ids)
        (by rw [hsI]; exact hfb)
      have hreqT : E.lg = true → ∀ p ∈ appliedTable γr A', ∃ x ∈ recs, x.1 = p.1 ∧
          tableReq (appliedTable γr A') x.1 = p.2 := by
        intro _ p hp
        obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hperm'.mem_iff.2 (List.mem_map.2 ⟨p, hp, rfl⟩))
        exact ⟨x, hx, hx1, by rw [hx1, tableReq_of_mem hnT' hp]⟩
      ihave Hpost := (srvSnapApplied_of_walk hGL hAt hDt hSRD hLk hGrant hCk hTTL hRv hMID hLead hTerm hFS hCIg s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl tI hmeta st b hle al ast lp cl x A hRO hwq R hpre hRok r hkI hbr hlp γp hrbw stp γd γt img nt hstp hnt halarm hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad hbuq A' hA' hany (srvIds E (appliedTable γr A').ids) recs U
        (tableReq (appliedTable γr A')) f rfl hUok' hbkG (fun _ => hfT) hreqT) $$ [Hw]
      · iframe #
        iframe Hw
      imod Hpost
      imodintro
      iapply HΦ
      iframe Hrcv Htk
      iapply (srvSnapAppliedM_of_G s ep sv γ ci E ρ γr d R r A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl hany)
      iexact Hpost
    -- a cluster that grants none (`specSnapM`'s premise until S2–S4): the image's lease bucket
    -- empty, the lessor revocable
    have Hlg0 := hlgE
    have hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅ :=
      imageLeasesAt_nil (hlnil hlgE) hleaseI
    ihave #Hlrev2 : lease.lessorRevocable E.γ.leases $$ []
    · have heq : lease.lessorModeIs (GF := GF) E.γ.leases (decide (E.lm = .mono)) =
          lease.lessorRevocable E.γ.leases := by
        rw [apply.AEnv.lm_of_lg_false hlgE]; rfl
      rw [← heq]; iexact Hlrev
    ihave HRS : E.RO (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) $$ [HRS]
    · rw [← srvRest_false E γr A Hlg0]; iexact HRS
    have hbe0 : backend.bktEnts (((backend.rbData d.P D).lookup go!"lease").getD ∅) =
        ([] : List (w64 × w64 × w64)).map lease.leaseRecEnc := by
      rw [hlease]
      exact List.eq_nil_of_length_eq_zero ((mvcc.bktEnts_length ∅).trans GMap.map_size_empty)
    have hids : srvIds E (appliedTable γr A').ids = [] := by simp [srvIds, hlgE]
    have hLr : ([] : List w64) = srvIds E (appliedTable γr A').ids := hids.symm
    have hUok : srvEverOk E A' (([] : List w64) ++ ([] : List (w64 × w64 × w64)).map (·.1)) :=
      ⟨fun _ => rfl, fun _ u hu => by simp at hu⟩
    have hbkG : ∀ n, membership.clusterBkts n ∨ restSet E.authMode n →
        (apply.restLeasesWith (fun _ => 0) (srvIds E (appliedTable γr A').ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup n =
        (<[go!"alarm" := ∅]> (<[go!"lease" := ((backend.rbData d.P D).lookup go!"lease").getD ∅]>
          (backend.rbData d.P D))).lookup n := by
      intro n hn
      rw [hids, apply.restLeasesWith_nil, hlease]
      exact snapRestImgM_bk E.authMode γr d.P D A' hany hA'.1 n hn
    iapply wp_fupd
    iapply (applySnapshot_walk hIES hLg hInfo hU64 hGI hGT hOSB hOn hSave hPut hBUR hID hName hSafe s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl hmmap tI hmeta hSB st b hle hLR al ast lp cl x A hRO hany (fun _ => authRecoverOn_glue hRec) false [] [] (fun _ => 0) [] []
      hbe0 (fun h => by cases h) (by simp) (fun h => by cases h) (by simp) List.Perm.nil
      (fun _ => ⟨rfl, rfl⟩) (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) hwq hRst hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL hCB hDel R hpre hRok r hcc hkI hbr hGTP hSTP hCIg γp hrbw hRel stp γd γt img nt hstp hnt hNAB hAR halarm halbi hlp hNAuB A' hauthI hNMB hCSB hmemb hClose hCRec memI himg hRAP hAP hMID γn t c rs dir ps idm hdir hdok hps hlid hNUA msi cs0 fg quota wad hbuq γnc hAG hLSR hUSR hWrite hTODO) $$ [Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRS Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR]
    · iframe #
      iframe Hrcv Hai Hat Hdsi Hlr Hbr Hfile Hpath Hst Hab HKV HRS Hkvc Hγt Htlive Hmsi Hcs0 HoOh Htk HauR
      rw [apply.ltHalf_false E [] hlgE, apply.everOwn_false E [] hlgE]
      simp only [List.map_nil]
      isplitr; · itrivial
      isplitr; · itrivial
      isplitr; · iintro !> -; iapply BigSepL.bigSepL_nil; iempintro
      iintro !>; iapply BigSepL.bigSepL_nil; iempintro
    iintro !> ⟨Hw, Hrcv, Htk⟩
    ihave Hpost := (srvSnapApplied_of_walk hGL hAt hDt hSRD hLk hGrant hCk hTTL hRv hMID hLead hTerm hFS hCIg s ep ap sn sv γ ci TM E ρ γr ai at0 dsi nc cfg ss hk hi d D lgh hkb hdbo hsop hP hcfgl tI hmeta st b hle al ast lp cl x A hRO hwq R hpre hRok r hkI hbr hlp γp hrbw stp γd γt img nt hstp hnt halarm hmemb memI himg γn t c rs dir ps idm hdir hdok hps hlid msi cs0 fg quota wad hbuq A' hA' hany [] [] [] (fun _ => 0) (fun _ => 0) hLr hUok hbkG
      (fun h => by rw [hlgE] at h; cases h) (fun h => by rw [hlgE] at h; cases h)) $$ [Hw]
    · iframe #
      iframe Hw
      unfold srvGrantIf; rw [hlgE]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    imod Hpost
    imodintro
    iapply HΦ
    iframe Hrcv Htk
    iapply (srvSnapAppliedM_of_G s ep sv γ ci E ρ γr d R r A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl hany)
    iexact Hpost

/-- **`applySnapshot.spec`** (J8b, 2026-11-01): `wp_proofEmpty` and `wp_proof_snapM` (since
2026-11-03; until then the mode-off `wp_proof_snap`). -/
theorem EtcdServer.applySnapshot.wp_proof
    (hIES : IsEmptySnap.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (hOSB : storage.OpenSnapshotBackend.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hBUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hSB : consistentIndex.SetBackend.spec (GF := GF) (hG := hG))
    (hLR : lease.lessor.Recover.spec (GF := GF) (hG := hG))
    (hRst : mvcc.watchableStore.Restore.spec (GF := GF) (hG := hG))
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hGTP : EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hSTP : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hRel : storage.storage.Release.spec (GF := GF) (hG := hG))
    (hNAB : schema.NewAlarmBackend.spec (GF := GF) (hG := hG))
    (hAR : v3alarm.AlarmStore.Recover.spec (GF := GF) (hG := hG))
    (hNAuB : schema.NewAuthBackend.spec (GF := GF) (hG := hG))
    (hNMB : schema.NewMembershipBackend.spec (GF := GF) (hG := hG))
    (hCSB : membership.RaftCluster.SetBackend.spec (GF := GF) (hG := hG))
    (hClose : backend.backend.Close.spec (GF := GF) (hG := hG))
    (hCRec : membership.RaftCluster.Recover.spec (GF := GF) (hG := hG))
    (hRAP : rafthttp.Transport.RemoveAllPeers.spec (GF := GF) (hG := hG))
    (hAP : rafthttp.Transport.AddPeer.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hNUA : EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG))
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hRec : auth.authStore.Recover.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG)) :
    EtcdServer.applySnapshot.spec (GF := GF) (hG := hG) :=
  ⟨EtcdServer.applySnapshot.wp_proofEmpty hIES,
    EtcdServer.applySnapshot.wp_proof_snapM hIES hLg hInfo hU64 hGI hGT hOSB hOn hSave hPut hBUR hID hName hSafe hSB hLR hRst hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL hCB hDel hGTP hSTP hCIg hRel hNAB hAR hNAuB hNMB hCSB hClose hCRec hRAP hAP hMID hNUA hGL hAt hDt hSRD hLk hGrant hCk hTTL hRv hLead hTerm hFS hAG hLSR hUSR hRec hWrite hTODO⟩

end proof

end EtcdGrove
end Perennial
