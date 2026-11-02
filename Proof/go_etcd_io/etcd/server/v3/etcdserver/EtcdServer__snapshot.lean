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
  intro s γ ci TM E ρ γr γw b ep st ai at' cs a t x toDisk ms γs nk sl γp ua q Hloop Hci Hrel
    Hpos Hsz Hwso
  cases toDisk
  all_goals (
  wp_start as ⟨#Hsrv, #Hsa, Hss, #Hfz, #Hnal, Hstor, #Hdisk, #Hal, #Hecs, #Hft, ⟨%kv, #Hkvf, #Hiskv⟩, #Hwp, Hai,
    Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, Hwt⟩
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
      iunfold isRNWal at Hsave
      icases Hsave with ⟨%si, %Hsieq, -, -, #HSaveSnap, -⟩
      simp only [interface.mkOk, GoInterface.ok.injEq] at Hsieq
      subst Hsieq
      iunfold rnWalTok at Hwt
      icases Hwt with ⟨%st0, #Hst0, Hwo⟩
      icombine Hstf Hst0 gives %Hsteq
      have Hsteq' : st0 = interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.storage.ty) #stp := by
        first | exact Hsteq.symm | exact Hsteq.2.symm
      subst Hsteq'
      ihave #Hm' : smOpt pm DFrac.discard (memSnapMade ai at' c []).Metadata' $$ []
      · iunfold smOpt; iright; iapply smPtsV_smPts $$ HmV
      ihave HSS := HSaveSnap
      ispecialize HSS $$ %q %snap' %pm %DFrac.discard %DFrac.discard
        %(memSnapMade ai at' c []).Metadata'
      wp_bind (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty)
        go!"SaveSnap" #stp)) (Val #snap'))
      iapply HSS $$ [Hwo]
      · iframe Hwo; iframe #
      inext
      iintro %serr ⟨Hwo, -, -, %Hserr⟩
      have hserr : serr = GoInterface.nil := by
        rcases Hserr with h | h
        · exact h
        · exact absurd Hwso h
      subst hserr
      ihave Hwt : rnWalTok (srvRAddr s) q $$ [Hwo]
      · iunfold rnWalTok; iexists _; iframe Hst0 Hwo
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
