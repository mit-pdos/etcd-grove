/-
**`EtcdServer.snapshot`'s body, proved** (D22 J4b, 2026-10-27): `EtcdServer.snapshot.specFull`
(`Spec/.../EtcdServer__snapshot.lean`) from its callees' specs. Not linked yet: `snapshot.spec`
(the axiom) stays what `snapshotIfNeededAndCompactRaftLog` uses until `specFull`'s premises reach
`applyAll` (`notes/decisions.md`, "D22 J4b"). Lean-first.

The walk (`server.go:2101-2153`): with `toDisk`, the `Info` log (the member id's string, the
applied and disk snapshot indices, `SnapshotCount`, `forceDiskSnapshot`), `forceDiskSnapshot :=
false`, `s.KV().Commit()` (its contract); `CreateSnapshot(ep.appliedi, ep.confState, nil)` over
the shared token and the registry (`CreateSnapshot.wp_reg`): `ErrSnapOutOfDate` returns
(`errors.Is` of a leaf error), any other error is not returned, so the `Panic` is dead;
`ep.memorySnapshotIndex := ep.appliedi`; `verifyConsistentIndexIsLatest(snap, ci)` (the consistent
index read through its interface, `wp_ci_get`); with `toDisk`, `SaveSnap` (`saveSnapOk`),
`ep.diskSnapshotIndex := ep.appliedi`, `Release` (the removal facts below `ai` from the applied
index's lower bound), the `Info` log.
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
instance notInterface_uint64_snapTake [FfiSyntax] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [ErrorStringLeaf]


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
theorem EtcdServer.snapshot.wp_proof_full
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
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
    EtcdServer.snapshot.specFull (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr γw b ep st ai at' cs a t x toDisk ms γs sl kv RC RC' ua Hloop Hci Hrel
  cases toDisk <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals (
  wp_start as ⟨#Hsrv, #Hsa, Hss, #Hfl, #Hreg, #Hdisk, #Hal, #Hkvf, Hkc, HRC, Hai, Hat, Hcs, Hst,
    Hbe, Happ, Hlr, HKV⟩
  iunfold isServer at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%sv, #Hfl'⟩, #Hat0, -, #Hrn⟩
  ihave #Hsci' := Hsci
  iunfold isServerCI at Hsci'
  icases Hsci' with ⟨#Hcif, #Hcii, #Hcinv⟩
  iunfold srvFieldsAt at Hfl'
  icases Hfl' with ⟨#Hlg, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -, -, -, -, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, -, -, -, -, #Hsc, -, -, -, -⟩
  iunfold srvSnapState at Hss
  icases Hss with ⟨%dsi, %msi, %f, Hdsi, Hmsi, Hf, %Hdm, #Hms, #Hro, Hak, %γss, #Htinv, #Hslb⟩
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
    -- `CreateSnapshot(ep.appliedi, ep.confState, nil)`
    iunfold epConfState at Hcs
    icases Hcs with ⟨Hcs, #Hcsok⟩
    ihave Hca : iprop(∃ oc : Option ConfStateM, memCsArg cs DFrac.discard oc) $$ []
    · iunfold epCsOk at Hcsok
      icases Hcsok with (%Hn | ⟨%c, #Hc⟩)
      · iexists none; iunfold memCsArg; ipureintro; exact Hn
      · iexists some c; iunfold memCsArg; iapply csPts_weaken; iexact Hc
    icases Hca with ⟨%oc, Hca⟩
    iunfold memFloorAtLeast at Hfl
    icases Hfl with ⟨%x, #Hft, %Hx⟩
    ihave #Hrinit := go_etcd_io.raft.v3.isInitialized_access $$ Praft
    unfold go_etcd_io.raft.v3.isInitialized
    icases Hrinit with ⟨%e1, %e2, %e3, %e4, %e5, %_, %_, %_, %_, %_, #Hrinit⟩
    iNamed Hrinit
    icases ErrSnapOOD with ⟨%eood, #Heood⟩
    iunfold EtcdGrove.errorsNewVar at ErrSnapOODNew
    icases ErrSnapOODNew with ⟨%xs, #Hxs, -⟩
    icombine Heood Hxs gives %Heq
    subst Heq
    ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    (try wp_auto)
    wp_apply (MemoryStorage.CreateSnapshot.wp_reg hCS ms γs γss x ai cs DFrac.discard oc slice.nil []
        _ Hx) $$ [Hak Hnil Hca] as %snap' %err ⟨Hak, -, #Hlbi, Hres⟩
    · iframe #; iframe
    icases Hres with (⟨%Herr, Hnil⟩ | ⟨%Herr, %σc, %tc, Hsnap⟩)
    · -- `ErrSnapOutOfDate`: `errors.Is` is `true`, return
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
      iframe HRC Hai Hat Hst Hbe Happ Hlr HKV
      isplitl [Hdsi Hmsi Hf Hak]
      · iunfold srvSnapState
        iexists dsi, msi, f
        iframe Hdsi Hmsi Hf Hms Hro Hak
        isplitr
        · ipureintro; exact Hdm
        iexists γss
        iframe Htinv Hlbi
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro; exact ⟨Hloop, rfl⟩
    · -- created at `ai`
      subst Herr
      imod ownSnapM_persist _ _ _ $$ Hsnap with #Hsnap
      (try wp_auto)
      -- `verifyConsistentIndexIsLatest(snap, s.consistIndex.ConsistentIndex())`
      wp_bind (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"ConsistentIndex"))
        (Val #()))
      iapply (wp_ci_get hCI γ ci b st Hloop.1) $$ [Hst Hbe]
      · iframe #; iframe
      iintro ⟨Hst, Hbe⟩
      wp_apply hVer snap' (memSnapCreated σc ai tc oc []) (ciEff γ st.k) Hci $$ []
      · iframe #
      (try wp_auto)
      iapply HΦ
      iexists stLoaded γ st
      obtain ⟨hlp, hlpp, hlc⟩ := stLoaded_facts_snap γ st
      iframe HRC Hai Hat Hst Hbe Happ Hlr HKV
      isplitl [Hdsi Hmsi Hf Hak]
      · iunfold srvSnapState
        iexists dsi, ai, f
        iframe Hdsi Hmsi Hf Hms Hro Hak
        isplitr
        · ipureintro; exact ⟨Hdm.1, Int.le_refl _⟩
        iexists γss
        iframe Htinv Hlbi
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro
      refine ⟨⟨by rw [hlp]; exact Hloop.1, by rw [hlpp, hlc]; exact Hloop.2⟩, hlc⟩
  · -- `toDisk`: the `Info` log, `forceDiskSnapshot := false`, `KV().Commit()`
    wp_apply hMID s sv.memberID $$ []
    · iframe #
    (try wp_auto)
    wp_apply hIDS sv.memberID as %ids -
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
    iunfold srvKVCommitOk at Hkc
    icases Hkc with ⟨%ki, %Hki, #Hkct⟩
    subst Hki
    (try wp_auto)
    wp_bind (App (Val #(methods ki.ty go!"Commit" ki.v)) (Val #()))
    iapply Hkct $$ HRC
    inext
    iintro HRC
    (try wp_auto)
    -- `CreateSnapshot(ep.appliedi, ep.confState, nil)`
    iunfold epConfState at Hcs
    icases Hcs with ⟨Hcs, #Hcsok⟩
    ihave Hca : iprop(∃ oc : Option ConfStateM, memCsArg cs DFrac.discard oc) $$ []
    · iunfold epCsOk at Hcsok
      icases Hcsok with (%Hn | ⟨%c, #Hc⟩)
      · iexists none; iunfold memCsArg; ipureintro; exact Hn
      · iexists some c; iunfold memCsArg; iapply csPts_weaken; iexact Hc
    icases Hca with ⟨%oc, Hca⟩
    iunfold memFloorAtLeast at Hfl
    icases Hfl with ⟨%x, #Hft, %Hx⟩
    ihave #Hrinit := go_etcd_io.raft.v3.isInitialized_access $$ Praft
    unfold go_etcd_io.raft.v3.isInitialized
    icases Hrinit with ⟨%e1, %e2, %e3, %e4, %e5, %_, %_, %_, %_, %_, #Hrinit⟩
    iNamed Hrinit
    icases ErrSnapOOD with ⟨%eood, #Heood⟩
    iunfold EtcdGrove.errorsNewVar at ErrSnapOODNew
    icases ErrSnapOODNew with ⟨%xs, #Hxs, -⟩
    icombine Heood Hxs gives %Heq
    subst Heq
    ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    (try wp_auto)
    wp_apply (MemoryStorage.CreateSnapshot.wp_reg hCS ms γs γss x ai cs DFrac.discard oc slice.nil []
        _ Hx) $$ [Hak Hnil Hca] as %snap' %err ⟨Hak, -, #Hlbi, Hres⟩
    · iframe #; iframe
    icases Hres with (⟨%Herr, Hnil⟩ | ⟨%Herr, %σc, %tc, Hsnap⟩)
    · -- `ErrSnapOutOfDate`: `errors.Is` is `true`, return
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
      iframe HRC Hai Hat Hst Hbe Happ Hlr HKV
      isplitl [Hdsi Hmsi Hf Hak]
      · iunfold srvSnapState
        iexists dsi, msi, false
        iframe Hdsi Hmsi Hf Hms Hro Hak
        isplitr
        · ipureintro; exact Hdm
        iexists γss
        iframe Htinv Hlbi
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro; exact ⟨Hloop, rfl⟩
    · -- created at `ai`
      subst Herr
      imod ownSnapM_persist _ _ _ $$ Hsnap with #Hsnap
      (try wp_auto)
      -- `verifyConsistentIndexIsLatest(snap, s.consistIndex.ConsistentIndex())`
      wp_bind (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"ConsistentIndex"))
        (Val #()))
      iapply (wp_ci_get hCI γ ci b st Hloop.1) $$ [Hst Hbe]
      · iframe #; iframe
      iintro ⟨Hst, Hbe⟩
      wp_apply hVer snap' (memSnapCreated σc ai tc oc []) (ciEff γ st.k) Hci $$ []
      · iframe #
      (try wp_auto)
      -- `SaveSnap`, `Release`
      iunfold srvSnapDisk at Hdisk
      icases Hdisk with ⟨%stp, %ss, %γd, %img, %Rm, %Hstp, #Hstf, #Hsave, #Hdinv, #Hrm⟩
      (try wp_auto)
      wp_bind (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty)
        go!"SaveSnap" #stp)) (Val #snap'))
      iunfold saveSnapOk at Hsave
      iapply Hsave $$ []
      · iexact Hsnap
      inext
      iintro -
      (try wp_auto)
      ihave #Hsnap' := Hsnap
      iunfold ownSnapM at Hsnap'
      icases Hsnap' with ⟨%ds, %pm, %uf, %Hnn, #HD, #Hd, #HM, #Hm, #Hpb⟩
      wp_apply hRel stp ss snap' pm DFrac.discard DFrac.discard
          (memSnapCreated σc ai tc oc []).Metadata' γd img Rm Hstp $$ [] as %rerr ⟨-, -, %Hrerr⟩
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
      wp_apply hGI pm DFrac.discard (memSnapCreated σc ai tc oc []).Metadata' $$ [] as -
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
      iframe HRC Hai Hat Hst Hbe Happ Hlr HKV
      isplitl [Hdsi Hmsi Hf Hak]
      · iunfold srvSnapState
        iexists ai, ai, false
        iframe Hdsi Hmsi Hf Hms Hro Hak
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
        iexists γss
        iframe Htinv Hlbi
      isplitl [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      ipureintro
      refine ⟨⟨by rw [hlp]; exact Hloop.1, by rw [hlpp, hlc]; exact Hloop.2⟩, hlc⟩

end proof

end EtcdGrove
end Perennial
