/-
**The new applier's options after `applySnapshot`, piece by piece** (D22 receiver epochs, S8d,
step 3's lemmas, `SnapApplyOpts.lean`): the lenses of the server's write right and rest resource
onto each object's backend part, the stores' contracts at the snapshot's backend, the KV, the hook,
and the server's own interfaces (`isRaftStatus`, `isSnapshotServer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ForceSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex

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

/-! ## The server's write right and rest resource lend each object's backend part -/

theorem srvRestRWH_lens_alarm (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al ast lp cl be))
      iprop(srvRestRW γB ∗ alarmBeOn al be) := by
  iunfold rwLens
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  isplitl [Hrw Hal]
  · iframe Hrw Hal
  iintro ⟨Hrw, Hal⟩
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hrw Hal Hau Hle Hcb

theorem srvRestRWH_lens_auth (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al ast lp cl be))
      iprop(srvRestRW γB ∗ authBeOn ast be) := by
  iunfold rwLens
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  isplitl [Hrw Hau]
  · iframe Hrw Hau
  iintro ⟨Hrw, Hau⟩
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hrw Hal Hau Hle Hcb

theorem srvRestRWH_lens_cluster (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al ast lp cl be))
      iprop(srvRestRW γB ∗ clusterBeOn cl be) := by
  iunfold rwLens
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  isplitl [Hrw Hcb]
  · iframe Hrw Hcb
  iintro ⟨Hrw, Hcb⟩
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hrw Hal Hau Hle Hcb

theorem srvRestOwnH_lens_cluster (M : auth.AuthMode) (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ roLens (GF := GF) (srvRestOwnH M γB cl (srvObjsOn al ast lp cl be))
      (fun r => iprop(srvRestOwn M γB cl r ∗ clusterBeOn cl be)) := by
  iunfold roLens
  iintro !> %r Hro
  iunfold srvRestOwnH at Hro
  iunfold srvObjsOn at Hro
  icases Hro with ⟨Hro, Hal, Hau, Hle, Hcb⟩
  dsimp only
  isplitl [Hro Hcb]
  · iframe Hro Hcb
  iintro %r' ⟨Hro, Hcb⟩
  iunfold srvRestOwnH
  iunfold srvObjsOn
  iframe Hro Hal Hau Hle Hcb

/-! ## The logger -/

/-- The new options' logger is the server's, not `nil` (`srvFieldsAt`'s). -/
theorem snap_lg_nn (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (lg : Loc) :
    isServerM on s γ ci TM E ρ γr ∗ srvLgAddr s ↦□ lg ⊢ ⌜lg ≠ null⌝ := by
  iintro ⟨#HS, #Hlg⟩
  iunfold isServerM at HS
  icases HS with ⟨-, -, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨#Hlg', %Hnn, -⟩
  icombine Hlg Hlg' gives %Heq
  ipureintro; rw [Heq]; exact Hnn

/-! ## The stores' contracts at the new backend -/

/-- (Strict M1, 2026-11-06) the restated contracts at the new backend `d'`, its write invariant
`W` (the store's `mvccW d'.gx`) and batch lock's `Pk`, its frozen hook `g`: the epoch's
`fun _ => Pk`, `g`, `srvBkTie d'` (`snapE`'s). (The mvcc merge, 2026-11-06: the auth store's and the
cluster's at any auth mode `M`, as `lean`'s P5/P6.2.) -/
theorem snap_isAlarmStore (al ast lp cl : Loc) (d' : mvcc.KBReal) (W Pk : IProp GF) (g : GoFunc)
    (hgnn : g ≠ func.nil) :
    alarmApplyOk al ∗ backend.isBackend d'.γB d'.P W Pk d'.be ∗ backend.plHookRO d'.γB g ⊢
    apply.isAlarmStore al (fun _ => Pk) g (srvBkTie d')
      (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#HalA, #HB, #Hhook⟩
  iunfold alarmApplyOk at HalA
  iapply HalA $$ %d' %W %Pk %g %(srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) HB Hhook [] []
  · ipureintro; exact hgnn
  · iapply srvRestRWH_lens_alarm

theorem snap_isAuthStore (M : auth.AuthMode) (al ast lp cl : Loc) (RD : IProp GF) (d' : mvcc.KBReal)
    (W Pk : IProp GF) (g : GoFunc) (hgnn : g ≠ func.nil) :
    authApplyOkM M ast RD ∗ backend.isBackend d'.γB d'.P W Pk d'.be ∗ backend.plHookRO d'.γB g ⊢
    apply.isAuthStore (auth.authIface ast) (fun _ => Pk) g (srvBkTie d') RD M
      (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#HisAuth, #HB, #Hhook⟩
  iunfold authApplyOkM at HisAuth
  iapply HisAuth $$ %d' %W %Pk %g %(srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) HB Hhook [] []
  · ipureintro; exact hgnn
  · iapply srvRestRWH_lens_auth

theorem snap_isCluster (M : auth.AuthMode) (al ast lp cl : Loc) (d' : mvcc.KBReal) (W Pk : IProp GF)
    (g : GoFunc) (hgnn : g ≠ func.nil) :
    clusterApplyOk cl ∗ backend.isBackend d'.γB d'.P W Pk d'.be ∗
      backend.plHookRO d'.γB g ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ⊢
    apply.isCluster cl (fun _ => Pk) g (srvBkTie d')
      (srvRestOwnH M d'.γB cl (srvObjsOn al ast lp cl d'.be))
      (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#Hisc, #HB, #Hhook, #Hvcn⟩
  iunfold clusterApplyOk at Hisc
  iapply Hisc $$ %M %d' %W %Pk %g %(srvRestOwnH M d'.γB cl (srvObjsOn al ast lp cl d'.be))
    %(srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) HB Hhook [] [] [] []
  · ipureintro; exact hgnn
  · iexact Hvcn
  · iapply srvRestOwnH_lens_cluster
  · iapply srvRestRWH_lens_cluster

/-- **The server's write right lends the lessor's checkpoint its put right** (`apply.isApplyLessor_of_lessorInv`'s
`RW` premise): the lessor's half of `le.b` and the `Lease` bucket's part of the write right's
buckets, given back at any buckets keeping `lease` present (the write right's buckets stay present,
`restPresent`; R4, 2026-11-07: until then `srvRestRWH_lessor`, without the give-back). -/
theorem srvRestRWH_lessorLens [go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ □ (srvRestRWH (GF := GF) γB (srvObjsOn al ast lp cl be) -∗
      lease.lessorBeOn lp be ∗ ∃ r, backend.rbPart γB (· = mvcc.leaseName) r ∗
        (∀ r', ⌜(r.lookup mvcc.leaseName).isSome → (r'.lookup mvcc.leaseName).isSome⌝ -∗
          lease.lessorBeOn lp be -∗ backend.rbPart γB (· = mvcc.leaseName) r' -∗
          srvRestRWH γB (srvObjsOn al ast lp cl be))) := by
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  iunfold srvRestRW at Hrw
  icases Hrw with ⟨%r, Hrw, %Hpr⟩
  ihave ⟨Hl, Hn⟩ := (backend.rbOwn_split (GF := GF) γB (· = mvcc.leaseName) r).1 $$ Hrw
  iframe Hle
  iexists r
  iframe Hl
  iintro %r' %hr' Hle Hl'
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hal Hau Hle Hcb
  iunfold srvRestRW
  rcases hlk : r'.lookup mvcc.leaseName with _ | v
  · -- no `lease` in `r'`, so none in `r`: `r` itself
    have hr0 : r.lookup mvcc.leaseName = none := by
      cases h : r.lookup mvcc.leaseName with
      | none => rfl
      | some _ => have := hr' (by rw [h]; rfl); rw [hlk] at this; cases this
    iexists r
    isplitl [Hl' Hn]
    · iapply (backend.rbOwn_split (GF := GF) γB (· = mvcc.leaseName) r).2
      iframe Hn
      iapply (backend.rbPart_congr (GF := GF) γB _ r' r
        (fun n hn => by subst hn; rw [hlk, hr0])).1 $$ Hl'
    ipureintro; exact Hpr
  · iexists r.insert mvcc.leaseName v
    isplitl [Hl' Hn]
    · iapply (backend.rbOwn_split (GF := GF) γB (· = mvcc.leaseName) (r.insert mvcc.leaseName v)).2
      isplitl [Hl']
      · iapply (backend.rbPart_congr (GF := GF) γB _ r' (r.insert mvcc.leaseName v)
          (fun n hn => by subst hn; rw [GMap.lookup_insert, hlk])).1 $$ Hl'
      · iapply (backend.rbPart_congr (GF := GF) γB _ r (r.insert mvcc.leaseName v)
          (fun n hn => by rw [GMap.lookup_insert_ne _ _ (Ne.symm hn)])).1 $$ Hn
    ipureintro
    intro n hn
    by_cases e : n = mvcc.leaseName
    · subst e; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact Hpr n hn

/-- **The new options' lessor** (R4, 2026-11-07: over mvcc's API, `apply.isApplyLessor_of_lessorInv`
as restated by R2, at the store's name `γ`, the tie `srvBkTie d'`, the batch lock `Pk` and hook `g`;
until then at mvcc's internal store names, `hookOk`, `storeWT`/`storeRT`): the revocation's lens
from the rest resource (`srvRestOwnH_lens_revoke`), the lessor's backend contract on `d'`
(`lessorApplyOk`, its `le.b` half lent by itself, `lessorBeOn_lens`), the checkpoint's put right
from the write right (`srvRestRWH_lessorLens`). -/
theorem snap_isApplyLessor [go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (M : auth.AuthMode) (al ast lp cl : Loc) (d' : mvcc.KBReal) (γ : mvcc.api.MvccName)
    (W Pk : IProp GF) (g : GoFunc) (hgnn : g ≠ func.nil) (hlp : mvcc.leaseParams d'.P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      lessorApplyOk lp ∗ lease.lessorCfg lp ∗ lessorLookupOk lp ∗
      lease.lessorInv lp (mvcc.api.mvccLeases γ) ∗
      backend.isBackend d'.γB d'.P W Pk d'.be ∗ backend.plHookRO d'.γB g ⊢
    apply.isApplyLessor (lease.lessorIface lp) γ (fun _ => Pk) g (srvBkTie d')
      (srvRestOwnH M d'.γB cl (srvObjsOn al ast lp cl d'.be))
      (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#Hpkg, #Hlbe, #Hlcfg, #Hllk, #Hlinv, #HB, #Hhook⟩
  ihave #Hlspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave #Hmvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  iapply apply.isApplyLessor_of_lessorInv hGL hAt hDt hSRD hLk hGrant hCk hTTL hRv lp γ
    (fun _ => Pk) g (srvBkTie d') (srvRestOwnH M d'.γB cl (srvObjsOn al ast lp cl d'.be))
    (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be))
  iunfold lessorLookupOk at Hllk
  iframe Hmvpkg Hlspkg Hlinv Hlcfg Hllk
  isplitr
  · -- the revocation's lens, at the tie's backend
    iunfold apply.revokeLens
    iintro !> %B %rs HBT HRO
    iunfold srvBkTie at HBT
    icases HBT with %hB
    subst hB
    ihave #Hl := srvRestOwnH_lens_revoke (GF := GF) B hlp M al ast lp cl
    icases Hl $$ %rs HRO with ⟨Hrb, %hlp', Hbe, Hcl⟩
    iframe Hrb Hbe Hcl
    isplitr
    · iunfold srvBkTie; ipureintro; rfl
    ipureintro; exact hlp'
  isplitr
  · -- the lessor's backend contract on the tie's backend
    iintro !> %B HBT
    iunfold srvBkTie at HBT
    icases HBT with %hB
    subst hB
    isplitr
    · iunfold srvBkTie; ipureintro; rfl
    unfold apply.bkWT
    rw [show mvcc.leaseName = go!"lease" from rfl]
    iunfold lessorApplyOk at Hlbe
    iapply Hlbe $$ %B %W %Pk %g %(lease.lessorBeOn lp B.be) HB Hhook [] []
    · ipureintro; exact hgnn
    · iapply lessorBeOn_lens
  · -- the checkpoint's put right, from the write right
    iintro !> %B HBT Hrw
    iunfold srvBkTie at HBT
    icases HBT with %hB
    subst hB
    isplitr
    · iunfold srvBkTie; ipureintro; rfl
    ihave #Hl := srvRestRWH_lessorLens (GF := GF) B.γB al ast lp cl B.be
    iapply Hl $$ Hrw

/-! (R4, 2026-11-07) `snap_isApplyKV` and `snap_hookOk` deleted: the options' KV is `isApplyKV`'s
`□ isMvcc` of the store's handle, kept by the restore; the hook is the environment's `f`. -/

/-! ## The server's own interfaces -/

/-- The server as the new options' `RaftStatusGetter`: from `srvFieldsAt`'s `memberID` and
`srvLeadInv`, and `srvAtomics`' term invariant. -/
theorem snap_isRaftStatus
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM on s γ ci TM E ρ γr ⊢
    apply.isRaftStatus (interface.mkOk EtcdServer.ty.PointerType #s) := by
  iintro ⟨#Hpkg, #HS⟩
  iunfold isServerM at HS
  icases HS with ⟨-, -, ⟨%v, #Hf⟩, #Hat, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, #Hlead, -⟩
  iunfold srvAtomicsM at Hat
  icases Hat with ⟨-, #Hti, -⟩
  iunfold apply.isRaftStatus
  iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> !> %Φ' - HΦ'
    iapply (hMID s v.memberID) $$ [] [HΦ']
    · iframe Hpkg Hmid
    inext; iintro -; iapply HΦ'; itrivial
  isplitr
  · iintro !> !> %Φ' - HΦ'
    iapply (hLead s) $$ [] [HΦ']
    · iframe Hpkg Hlead
    inext; iintro %l -; iapply HΦ'; itrivial
  · iintro !> !> %Φ' - HΦ'
    iapply (hTerm s) $$ [] [HΦ']
    · iframe Hti Hpkg
    inext; iintro %t' -; iapply HΦ'; itrivial

/-- The server as the new options' `SnapshotServer`, under the environment's `FS` (`srvEnvOk`'s
`E.FS = srvFS s`). -/
theorem snap_isSnapshotServer
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM on s γ ci TM E ρ γr ⊢
    apply.isSnapshotServer (interface.mkOk EtcdServer.ty.PointerType #s) E.FS := by
  iintro ⟨#Hpkg, #HS⟩
  iunfold isServerM at HS
  icases HS with ⟨-, -, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, %Henv, -⟩
  rw [Henv.1]
  iunfold apply.isSnapshotServer
  iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
  isplitr
  · ipureintro; rfl
  iintro !> !> %Φ' Hfs HΦ'
  iapply (hFS s) $$ [Hfs] [HΦ']
  · iframe Hpkg; iframe Hfs
  inext; iintro Hfs; iapply HΦ'; iexact Hfs

/-! ## The consistent indexer -/

/-- The consistent index as the new options' indexer, over `srvCiC`'s loaded states (`wp_ci_get`
returns `stLoaded γ st`, which is `st` for them; D22 receiver epochs, S8d, 2026-10-26: `srvCiC`
admitted unloaded states until then, over which the contract is false once `γ.m0.1 ≠ 0`, after a
snapshot). -/
theorem snap_isConsistentIndexer
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : ApplyNames) (ci : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerCI s γ ci ⊢
    apply.isConsistentIndexer (ciIface ci) (srvCiC γ ci) := by
  iintro ⟨#Hpkg, #HCI⟩
  ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex
    $$ []
  · iPkgInit
  iunfold isServerCI at HCI
  icases HCI with ⟨-, #HisCI, #Hcons⟩
  iunfold apply.isConsistentIndexer
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩
  isplitr
  · ipureintro; rfl
  iintro !> %C %x %HC
  obtain ⟨cst, cb, hC, hcp, hld, hx⟩ := HC
  subst hC hx
  iintro %Φ' !> Hpre HΦ'
  iapply (wp_wand (Φ := fun w => iprop((
      iprop(applyThread γ cst ∗ applyBackend γ ci cb) -∗ Φ' #(ciEff γ cst.k)) ∗
      (⌜w = #(ciEff γ cst.k)⌝ ∗ applyThread γ cst ∗ applyBackend γ ci cb))))
    $$ [Hpre HΦ']
  · iapply (wp_frame_step_l' (by rfl) Std.LawfulSet.subset_refl)
    iframe HΦ'
    icases Hpre with ⟨Hcst, Hcb⟩
    iapply (wp_ci_get hCIg γ ci cb cst hcp) $$ [Hcst Hcb]
    · iframe Hcipkg Hcons HisCI; iframe Hcst Hcb
    iintro ⟨Hcst, Hcb⟩
    rw [hld]
    iframe Hcst Hcb
    ipureintro; rfl
  · iintro %w ⟨HΦ', %Hw, HP⟩
    subst Hw
    iapply HΦ' $$ HP

end proof
end EtcdGrove
end Perennial
