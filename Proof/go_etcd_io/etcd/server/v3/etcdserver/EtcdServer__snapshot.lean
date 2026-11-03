/-
`EtcdServer.snapshot` (2026-10-30, the repair: a theorem, until then the trust-boundary axiom;
2026-10-31, the snapshot track: proved, lean's old proof (`SnapTakeProof.lean`, deleted) rewired over `CreateSnapshot`'s
registry-free spec, the snapshot certified by `srv_snap_make`).

The walk (`server.go:2107-2160`): with `toDisk`, the `Info` log (the member id's string, the
applied and disk snapshot indices, `SnapshotCount`, `forceDiskSnapshot`), `forceDiskSnapshot :=
false`, `s.KV().Commit()` (its contract); `CreateSnapshot(ep.appliedi, ep.confState, nil)`, its
snapshot certified first (`srv_snap_make`: registered in the cluster's registry, so valid):
`ErrSnapOutOfDate` returns (`errors.Is` of a leaf error), any other error is not returned, so the
`Panic` is dead; `ep.memorySnapshotIndex := ep.appliedi`; `verifyConsistentIndexIsLatest(snap,
ci)` (the consistent index read through its interface, `wp_ci_get`); with `toDisk`, `SaveSnap`
(`saveSnapOk`), `ep.diskSnapshotIndex := ep.appliedi`, `Release` (the removal facts below `ai` from
the applied index's lower bound), the `Info` log.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.verifyConsistentIndexIsLatest
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Release
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Bool
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapCert
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Commit

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
  go_etcd_io.etcd.server.v3.etcdserver.cindex

/-- `uint64` is not an interface type (as `InvStart.lean`'s: `String()` on a `types.ID`). -/
instance notInterface_uint64_snapshot [GooseExts] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Loading `ci` changes only `k`, and not `ciEff` (`EtcdServer__apply.lean`'s `stLoaded_facts`). -/
theorem stLoaded_facts_snap (γ : ApplyNames) (st : ApplyState) :
    (stLoaded γ st).pending = st.pending ∧ (stLoaded γ st).p = st.p ∧
      ciEff γ (stLoaded γ st).k = ciEff γ st.k := by
  unfold stLoaded
  split
  · rename_i h
    refine ⟨rfl, rfl, ?_⟩
    unfold ciEff
    rw [ite_eq_left h]
    split <;> rfl
  · exact ⟨rfl, rfl, rfl⟩

/-- (2026-11-03, R2b-1 stage 5) A committed log `L` of length `n` ending at the term `t`, a prefix of
the handed log `lw`: `lw`'s entry at `n` has the term `t` (what the apply thread's `SaveSnap` at
`n` takes, `rnDur_ownSnap_au`). -/
theorem snap_handed_entry (L lw : List LogEntry) (n : Nat) (tm : w64) (hlen : L.length = n)
    (hpos : 0 < n) (hlast : L.getLast?.map LogEntry.term = some tm) (hpfx : L <+: lw) :
    ∃ e : LogEntry, lw[n - 1]? = some e ∧ e.term = tm := by
  obtain ⟨u, rfl⟩ := hpfx
  cases hl : L.getLast? with
  | none => rw [hl] at hlast; cases hlast
  | some x =>
    rw [hl] at hlast
    refine ⟨x, ?_, Option.some.inj hlast⟩
    rw [List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?, hlen] at hl
    exact hl

set_option maxHeartbeats 1600000 in
theorem EtcdServer.snapshot.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG))
    (hCS : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hCI : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hVer : verifyConsistentIndexIsLatest.spec (GF := GF) (hG := hG))
    (hRel : storage.storage.Release.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hBool : zap.Bool.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshot.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr γw b ep st ai at' cs a t x toDisk ms γs nk sl γp ua q γn Hloop Hci Hrel
    Hpos Hsz Hwso Hγn Hpre
  cases toDisk
  all_goals (
  wp_start as ⟨#Hsrv, #Hsa, Hss, #Hfz, #Hnal, Hstor, #Hdisk, #Hal, #Hecs, #Hft, ⟨%kv, #Hkvf, #Hiskv⟩, #Hwp, Hai,
    Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, Hwt, #Hwh⟩
  -- (R2b-1 stage 5) the applied log's committed lower bound, kept from `srvSnapStor`
  iunfold srvSnapStor at Hstor
  icases Hstor with ⟨Hmsi, #Hncl, #Hrli, ⟨%Aw, #HAw, %HAwp⟩⟩
  ihave Hstor : srvSnapStor ms γs γr nk ai at' $$ [Hmsi]
  · iunfold srvSnapStor; iframe Hmsi Hncl Hrli; iexists Aw; iframe HAw; ipureintro; exact HAwp
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%sv, #Hfl'⟩, #Hat0, -, #Hrn⟩
  ihave #Hsci' := Hsci
  iunfold isServerCI at Hsci'
  icases Hsci' with ⟨#Hcif, #Hcii, #Hcinv⟩
  iunfold srvFieldsAtM at Hfl'
  icases Hfl' with ⟨#Hlg, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -, -, -, -, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, -, -, -, -, #Hsc, -, -, -, -⟩
  iunfold srvSnapState at Hss
  icases Hss with ⟨%d, %m, %f, Hd, Hm, Hf, %Hdm, #Hms, #Hlb⟩
  ihave #Hlb0 := memSnapLb_mono γs (uint.nat sl) 0 (Nat.zero_le _) $$ Hlb
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Praft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Ptypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Pcix : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Prpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Pstor : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  wp_auto
  wp_apply hLg s sv.lg $$ [$Hlr] as ⟨-, Hlr⟩
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto))
  · -- no disk: straight to `CreateSnapshot`
    iunfold epConfState at Hcs
    icases Hcs with ⟨Hcs, #Hcsok⟩
    ihave #Hrinit := go_etcd_io.raft.v3.isInitialized_access $$ Praft
    unfold go_etcd_io.raft.v3.isInitialized
    icases Hrinit with ⟨%e1, %e2, %e3, %e4, %e5, %_, %_, %_, %_, %_, #Hrinit⟩
    iNamed Hrinit
    icases ErrSnapOOD with ⟨%eood, #Heood⟩
    iunfold EtcdGrove.errorsNewVar at ErrSnapOODNew
    icases ErrSnapOODNew with ⟨%xs, #Hxs, -⟩
    icombine Heood Hxs gives %Heq
    subst Heq
    (try wp_auto)
    wp_apply (wp_srv_createSnapshot hCS ms γs γr nk ai at' cs _ Hpos Hsz) $$ [Hstor]
      as %snap' %err ⟨#Hlbi, Hres⟩
    · iframe #; iframe Hstor
    icases Hres with (⟨%Herr, %c, %Hcsc, Hsnap⟩ | %Herr)
    rotate_left
    · -- `ErrSnapOutOfDate`: `errors.Is` is `true`, return
      obtain ⟨-, Herr⟩ := Herr
      subst Herr
      (try wp_auto)
      obtain ⟨Hptr, Hleaf, HnoIs⟩ := errorString_leaf xs
      wp_apply hIs (· = interface.mkOk
          (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xs) (fun _ => False)
          _ _ (fun tii h => by cases h; exact Hptr)
          (_root_.Perennial.errors.treeTyped_pointer _ _ Hptr) $$ []
        as %bis ⟨-, %Hb, -⟩
      · iframe #
        isplitl
        · iapply _root_.Perennial.errors.errorIsTree_leaf _ (fun _ => False) _ Hleaf HnoIs
        ipureintro; rfl
      rw [Hb _ rfl Hptr rfl]
      (try wp_auto)
      iapply HΦ
      iexists st
      iframe Hai Hat Hst Hbe Happ Hlr HKV Hfz Hwt
      isplitl [Hd Hm Hf]
      · iunfold srvSnapState
        iexists d, m, f
        iframe Hd Hm Hf Hms Hlbi
        ipureintro; exact Hdm
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro; exact ⟨Hloop, rfl⟩
    · -- created at `ai`
      subst Herr
      imod ownSnapV_persist _ _ _ $$ Hsnap with #HsnapV
      ihave #Hsnap := ownSnapV_M _ _ _ $$ HsnapV
      (try wp_auto)
      -- `verifyConsistentIndexIsLatest(snap, s.consistIndex.ConsistentIndex())`
      wp_bind (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"ConsistentIndex"))
        (Val #()))
      iapply (wp_ci_get hCI γ ci b st Hloop.1) $$ [Hst Hbe]
      · iframe #; iframe
      iintro ⟨Hst, Hbe⟩
      wp_apply hVer snap' (memSnapMade ai at' c []) (ciEff γ st.k) (by exact Hci) $$ []
      · iframe #
      (try wp_auto)
      iapply HΦ
      iexists stLoaded γ st
      obtain ⟨hlp, hlpp, hlc⟩ := stLoaded_facts_snap γ st
      iframe Hai Hat Hst Hbe Happ Hlr HKV Hfz Hwt
      isplitl [Hd Hm Hf]
      · iunfold srvSnapState
        iexists d, ai, f
        iframe Hd Hm Hf Hms Hlbi
        ipureintro; exact ⟨Hdm.1, Int.le_refl _⟩
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro
      refine ⟨⟨by rw [hlp]; exact Hloop.1, by rw [hlpp, hlc]; exact Hloop.2⟩, hlc⟩
  · -- `toDisk`: the `Info` log, `forceDiskSnapshot := false`, `KV().Commit()`
    wp_apply hMID s sv.memberID $$ []
    · iframe #
    (try wp_auto)
    -- (`wp_apply_core`: `wp_apply` would resolve `zap.String` too, the receipt's step)
    wp_apply_core hIDS sv.memberID
    · iPkgInit
    iintro %ids -
    -- (S6) a Go step gives a time receipt, for the commit's write token
    repeat (
      fail_if_success wp_bind (App (Val (GoInstruction _)) (Val _))
      first | wp_pure | wp_load | wp_store | wp_alloc_auto)
    wp_bind (App (Val (GoInstruction _)) (Val _))
    iapply wp_go_step_receipt'
    case hv => first | rfl | simp [val.isPanic] | decide | exact isPanic_intoVal _
    inext
    iintro Hr Hlc
    iapply wp_value'
    wp_apply hStr as %f0 -
    (try wp_auto)
    wp_apply hU64 as %f1 -
    (try wp_auto)
    wp_apply hU64 as %f2 -
    (try wp_auto)
    wp_apply hU64 as %f3 -
    (try wp_auto)
    wp_apply hBool as %f4 -
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hLg s sv.lg $$ [$Hlr] as ⟨-, Hlr⟩
    · iframe #; ipureintro; exact Hlgnn
    wp_apply hInfo sv.lg $$ []
    · iframe #; ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply hKV s kv $$ []
    · iframe #
    -- (S6) `Commit()`: the writer's tokens lent by the row, a write token from the budget
    imod srvApplyKVCore_commit s E γw x ua γp $$ Hwp Hr Hlc HKV with ⟨Hwf, Hwo, Hwt, HKVc⟩
    ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
    · iPkgInit
    ihave Hkc := srvKVCommitOk_of_kv hC kv E.s E.γ iprop(True) iprop(True) iprop(True)
      $$ [$Hmpkg $Hiskv]
    ihave Hsrq := mvcc.storeReq_true (GF := GF) E.γ
    iunfold srvKVCommitOk at Hkc
    icases Hkc with ⟨%ki, %Hki, #Hkct⟩
    subst Hki
    (try wp_auto)
    wp_bind (App (Val #(methods ki.ty go!"Commit" ki.v)) (Val #()))
    iapply Hkct $$ [Hwf Hwo Hwt Hsrq]
    · iframe Hwf Hwo Hwt Hsrq
    inext
    iintro ⟨Hwf, Hwo, -, -⟩
    ihave HKV := HKVc $$ [Hwf Hwo]
    · iframe Hwf Hwo
    (try wp_auto)
    -- `CreateSnapshot(ep.appliedi, ep.confState, nil)`
    iunfold epConfState at Hcs
    icases Hcs with ⟨Hcs, #Hcsok⟩
    ihave #Hrinit := go_etcd_io.raft.v3.isInitialized_access $$ Praft
    unfold go_etcd_io.raft.v3.isInitialized
    icases Hrinit with ⟨%e1, %e2, %e3, %e4, %e5, %_, %_, %_, %_, %_, #Hrinit⟩
    iNamed Hrinit
    icases ErrSnapOOD with ⟨%eood, #Heood⟩
    iunfold EtcdGrove.errorsNewVar at ErrSnapOODNew
    icases ErrSnapOODNew with ⟨%xs, #Hxs, -⟩
    icombine Heood Hxs gives %Heq
    subst Heq
    (try wp_auto)
    wp_apply (wp_srv_createSnapshot hCS ms γs γr nk ai at' cs _ Hpos Hsz) $$ [Hstor]
      as %snap' %err ⟨#Hlbi, Hres⟩
    · iframe #; iframe Hstor
    icases Hres with (⟨%Herr, %c, %Hcsc, Hsnap⟩ | %Herr)
    rotate_left
    · -- `ErrSnapOutOfDate`: `errors.Is` is `true`, return
      obtain ⟨-, Herr⟩ := Herr
      subst Herr
      (try wp_auto)
      obtain ⟨Hptr, Hleaf, HnoIs⟩ := errorString_leaf xs
      wp_apply hIs (· = interface.mkOk
          (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xs) (fun _ => False)
          _ _ (fun tii h => by cases h; exact Hptr)
          (_root_.Perennial.errors.treeTyped_pointer _ _ Hptr) $$ []
        as %bis ⟨-, %Hb, -⟩
      · iframe #
        isplitl
        · iapply _root_.Perennial.errors.errorIsTree_leaf _ (fun _ => False) _ Hleaf HnoIs
        ipureintro; rfl
      rw [Hb _ rfl Hptr rfl]
      (try wp_auto)
      iapply HΦ
      iexists st
      iframe Hai Hat Hst Hbe Happ Hlr HKV Hfz Hwt
      isplitl [Hd Hm Hf]
      · iunfold srvSnapState
        iexists d, m, false
        iframe Hd Hm Hf Hms Hlbi
        ipureintro; exact Hdm
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro; exact ⟨Hloop, rfl⟩
    · -- created at `ai`
      subst Herr
      imod ownSnapV_persist _ _ _ $$ Hsnap with #HsnapV
      ihave #Hsnap := ownSnapV_M _ _ _ $$ HsnapV
      (try wp_auto)
      -- `verifyConsistentIndexIsLatest(snap, s.consistIndex.ConsistentIndex())`
      wp_bind (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"ConsistentIndex"))
        (Val #()))
      iapply (wp_ci_get hCI γ ci b st Hloop.1) $$ [Hst Hbe]
      · iframe #; iframe
      iintro ⟨Hst, Hbe⟩
      wp_apply hVer snap' (memSnapMade ai at' c []) (ciEff γ st.k) (by exact Hci) $$ []
      · iframe #
      (try wp_auto)
      -- `SaveSnap`, `Release`
      iunfold srvSnapDisk at Hdisk
      icases Hdisk with ⟨%stp, %ss, %γd, %img, %Rm, %Hstp, #Hstf, #Hsave, #Hdinv, #Hrm⟩
      (try wp_auto)
      ihave #Hsnap' := HsnapV
      iunfold ownSnapV at Hsnap'
      icases Hsnap' with ⟨%ds, %pm, %uf, %Hnn, #HD, #Hd', #HM, #HmV, #Hpb⟩
      -- (2026-10-31) the WAL contract's `SaveSnap`, at the apply thread's share of the WAL
      ihave %Hsok := isWalStorage_ok _ $$ Hsave
      obtain ⟨si, Hsieq⟩ := Hsok
      ihave #HSaveSnap := walSaveSnap_spec _ si Hsieq q snap' pm DFrac.discard DFrac.discard
        (memSnapMade ai at' c []).Metadata' (token γn.wal.app) $$ Hsave
      simp only [interface.mkOk, GoInterface.ok.injEq] at Hsieq
      subst Hsieq
      iunfold rnWalTokA at Hwt
      icases Hwt with ⟨%st0, #Hst0, Hwo, Hwap, #Hdur⟩
      icombine Hstf Hst0 gives %Hsteq
      have Hsteq' : st0 = interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.storage.ty) #stp := by
        first | exact Hsteq.symm | exact Hsteq.2.symm
      subst Hsteq'
      ihave #Hm' : smOpt pm DFrac.discard (memSnapMade ai at' c []).Metadata' $$ []
      · iunfold smOpt; iright; iapply smPtsV_smPts $$ HmV
      -- (R2b-1 stage 5) the `SaveSnap` as the WAL contract's atomic update (`rnDur_ownSnap_au`):
      -- the handed log holds the snapshot's index at its term (the applied log's, committed)
      iunfold rnWalHanded at Hwh
      icases Hwh with ⟨%lw, #Hwlb, #Hwc, %Hwn⟩
      iunfold srvRLogLb at HAw
      icases HAw with ⟨#HAc, -⟩
      ihave %Hag := isCommittedLogLb_agree γr.raft.raft.cl _ lw $$ [HAc Hwc]
      · rw [← Hγn]; iframe HAc Hwc
      obtain ⟨HAlen, HAlast⟩ := HAwp
      have hLlen : (srvLE γr.raft Aw).length = uint.nat ai := by
        simp only [srvLE, Hpre, List.nil_append, List.length_map]; word
      have hpos' : 0 < uint.nat ai := by word
      have hLpfx : srvLE γr.raft Aw <+: lw := by
        rcases Hag with h | h
        · exact h
        · have := h.length_le
          have hq : lw = srvLE γr.raft Aw := h.eq_of_length (by omega)
          rw [hq]; exact List.prefix_refl _
      have hAne : Aw ≠ [] := by intro h0; rw [h0] at HAlen; simp at HAlen; word
      have hLlast : (srvLE γr.raft Aw).getLast?.map LogEntry.term = some at' := by
        rcases HAlast with h0 | h0
        · exact absurd h0 hAne
        · simp only [srvLE, Hpre, List.nil_append, List.getLast?_map, Option.map_map]
          simpa [EntryModel.toLE, Function.comp_def] using h0
      obtain ⟨e, He, Het⟩ := snap_handed_entry _ lw _ at' hLlen hpos' hLlast hLpfx
      ihave HAU := rnDur_ownSnap_au γn.wal _ (memSnapMade ai at' c []).Metadata' lw e
        (by simpa [memSnapMade] using hpos') (by simpa [memSnapMade] using He)
        (by simpa [memSnapMade] using Het) $$ Hdur Hwap Hwlb
      wp_bind (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty)
        go!"SaveSnap" #stp)) (Val #snap'))
      iapply HSaveSnap $$ [Hwo HAU]
      · iframe Hwo HAU; iframe #
      inext
      iintro %serr ⟨Hwo, -, -, Hres⟩
      icases Hres with (⟨%Hserr, Hwap⟩ | %Hbad)
      rotate_left
      · exact absurd Hwso Hbad
      subst Hserr
      ihave Hwt : rnWalTokA γn (srvRAddr s) q $$ [Hwo Hwap]
      · iunfold rnWalTokA; iexists _; iframe Hst0 Hwo Hwap Hdur
      (try wp_auto)
      wp_apply hRel stp ss snap' pm DFrac.discard DFrac.discard
          (memSnapMade ai at' c []).Metadata' γd img Rm Hstp $$ [] as %rerr ⟨-, -, %Hrerr⟩
      · iframe #
        iintro !> %j %hj
        iapply Hrm
        iunfold appliedAtLeast at Hal
        iapply monoNatLbOwn_le (uint.nat j + 1) (by
          have h : uint.Z j < uint.Z ai := hj
          have := uint_nat_eq j
          have := uint_nat_eq ai
          omega) $$ Hal
      have hrerr : rerr = GoInterface.nil := by
        rcases Hrerr with h | h
        · exact h
        · exact absurd Hrel h
      subst hrerr
      (try wp_auto)
      wp_apply hGI pm DFrac.discard (memSnapMade ai at' c []).Metadata' $$ [] as -
      · iframe #
      wp_apply hU64 as %f5 -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl2 ⟨-, -⟩
      (try wp_auto)
      wp_apply hInfo sv.lg $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      iexists stLoaded γ st
      obtain ⟨hlp, hlpp, hlc⟩ := stLoaded_facts_snap γ st
      iframe Hai Hat Hst Hbe Happ Hlr HKV Hfz Hwt
      isplitl [Hd Hm Hf]
      · iunfold srvSnapState
        iexists ai, ai, false
        iframe Hd Hm Hf Hms Hlbi
        ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro
      refine ⟨⟨by rw [hlp]; exact Hloop.1, by rw [hlpp, hlc]; exact Hloop.2⟩, hlc⟩

end proof

end EtcdGrove
end Perennial
