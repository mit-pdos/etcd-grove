/-
**The disabled auth store's server contracts** (the authstore-noax stage, 2026-11-18;
`notes/decisions.md`, "authstore-noax"). Lean-first (no Rocq counterpart).

Of the disabled store's invariant (`auth.offInv`, `auth/OffInv.lean`): its `Recover` on a later
backend (`authRecoverOk`), over schema's auth backend on the real backend: the read transaction
begun with the idle part of the new backend's auth buckets reads them (`backend.readTx.RLock.specIdle`),
the `auth` bucket at `authBoot` (no `authEnabled` key: `false`; the revision `1`), the users' empty
(`backend.readTx.UnsafeForEach.spec`: no user, so no record decoded).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal
public import Proof.go_etcd_io.etcd.server.v3.auth.OffInv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__AuthInfoFromTLS
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock_idle
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeReadAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeReadAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeGetAllUsers
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__IsSafeRangeBucket

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `authBoot` has no `authEnabled` key. -/
theorem authBoot_enabled : (authBoot : backend.BktData).lookup schema.authEnabledKey = none := by
  unfold authBoot schema.authEnabledKey
  rw [GMap.lookup_insert_ne _ _ (by decide)]
  rfl

/-- `authBoot`'s revision is 8 bytes. -/
theorem authBoot_revWf : schema.revWf (authBoot : backend.BktData) := by
  intro v hv
  unfold authBoot schema.authRevisionKey at hv
  rw [GMap.lookup_insert] at hv
  injection hv with hv
  subst hv
  simp only [u64Be, List.length_reverse, u64Le_length]

/-- **The disabled store's `Recover`** (`authRecoverOk`). -/
theorem authRecoverOk_off
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.specIdle (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hEn : schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authReadTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (stl : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      auth.offInv stl ⊢ authRecoverOk stl := by
  iintro ⟨#Hpkg, #Hspkg, #Hinv⟩
  iunfold authRecoverOk
  iintro !> %oldbe %abl %lg %dn %W %Pk %qo %r %Φ !> ⟨HbeOn, %Hlg, #Habbe, #Hablg, #HB, Ho, Hpool,
    Htt, Hrb, %Hr, %Hhas⟩ HΦ
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold auth.offInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, #HbeG, #HenG, -⟩
  iunfold authBeOn at HbeOn
  icases HbeOn with ⟨%abl0, %lg0, %Hlg0, Hbe, -, -⟩
  wp_method_call
  wp_call
  (try wp_auto)
  -- replace the backend under `beMu`'s write lock
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$HbeG] as ⟨Hlk, HP⟩
  iunfold auth.offBeP at HP
  icases HP with ⟨%be1, Hbe'⟩
  icombine Hbe Hbe' gives %Heq
  subst Heq
  ihave Hbe := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hbe Hbe']
  · iframe
  (try wp_auto)
  ihave ⟨Hbe, Hbe'⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hbe
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hbe']
  · inext; iunfold auth.offBeP; iexists (authBkIface abl); iexact Hbe'
  (try wp_auto)
  -- `be.ReadTx()`: schema's, over the new backend's read transaction
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (hRT dn.γB dn.P W Pk dn.be) $$ [$Hbpkg $HB] as %rt #Hrt
  wp_alloc l as Hl
  iStructNamed Hl
  irename tx => Htxf
  irename lg => Hlgf
  ipersist Htxf
  ipersist Hlgf
  wp_auto_lc 1
  -- `tx.RLock()`: a reader's slot borrowed, the idle part's view
  iunfold backend.bkRPool at Hpool
  icases Hpool with ⟨#Hrp, Hrs⟩
  imod backend.rdTok_borrow dn.γB dn.P dn.be ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hrp $Htt]
    with ⟨Hr, Hloan⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hr with Hr
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (hRL dn.γB dn.P W Pk dn.be rt qo auth.authBkts r) $$ [$Hbpkg $HB $Hrt $Hr $Ho $Hrb]
    as ⟨%rtx, %rv, Hh, Ho, Hrb, %Hag⟩
  have hag : ∀ n, (n = mvcc.authBI.name ∨ n = mvcc.authUsersBI.name ∨ n = mvcc.authRolesBI.name) →
      ∀ k, backend.vOf dn.P rv n k = ((r.lookup n).getD ∅).lookup k := by
    intro n hn; apply Hag n
    rcases hn with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  ihave #Hrd := schema.read_authReader hUR hID hName hSafe dn.γB dn.P W Pk dn.be rt rtx rv r Hhas hag
    $$ [$Hspkg $Hbpkg $HB $Hrt]
  (try wp_auto)
  have hauth : (schema.authDataR r).auth = authBoot := Hr.1
  have husers : (schema.authDataR r).users = ∅ := Hr.2
  -- `UnsafeReadAuthEnabled()`: `false` (no `authEnabled` key in `authBoot`)
  wp_apply (hEn l ⟨go.GoType.PointerType storage.backend.readTx.ty, #rt⟩ (backend.rtHeld dn.γB dn.P dn.be rtx rv)
      (schema.authDataR r)) $$ [$Hspkg $Htxf $Hrd $Hh] as %enb ⟨Hh, %Henb⟩
  have henb : enb = false := by
    rw [Henb]; unfold schema.enabledOf; rw [hauth, authBoot_enabled]; decide
  subst henb
  (try wp_auto)
  -- `setRevision(UnsafeReadAuthRevision())`
  wp_apply (hRev l ⟨go.GoType.PointerType storage.backend.readTx.ty, #rt⟩ (backend.rtHeld dn.γB dn.P dn.be rtx rv)
      (schema.authDataR r) (by rw [hauth]; exact authBoot_revWf)) $$ [$Hspkg $Htxf $Hrd $Hh]
    as %rv0 ⟨Hh, -⟩
  wp_apply (auth.setRevision_off stl rv0) $$ [$Hpkg $Hinv]
  (try wp_auto)
  -- `refreshRangePermCache(tx)`: no user
  have hnone : ∀ k, backend.vOf dn.P rv mvcc.authUsersBI.name k = none := by
    intro k
    rw [hag _ (Or.inr (Or.inl rfl)) k]
    have : (r.lookup mvcc.authUsersBI.name).getD ∅ = ∅ := husers
    rw [this]; rfl
  ihave #HFE := schema.read_forEachUsersEmpty hFE hID hName hSafe dn.γB dn.P W Pk dn.be rt rtx rv
    Hhas.2.1 hnone $$ [$Hspkg $Hbpkg $HB $Hrt]
  ihave #HGA : auth.getAllUsersNone ⟨go.GoType.PointerType storage.schema.authReadTx.ty, #l⟩
      (backend.rtHeld dn.γB dn.P dn.be rtx rv) $$ []
  · iunfold auth.getAllUsersNone
    iintro !> %Φ' !> HH HΦ'
    iapply (hGA l lg ⟨go.GoType.PointerType storage.backend.readTx.ty, #rt⟩ (backend.rtHeld dn.γB dn.P dn.be rtx rv))
      $$ [$Hspkg $Htxf $Hlgf $HH $HFE]
    iexact HΦ'
  wp_apply (auth.refreshRangePermCache_off h_Debug stl
      ⟨go.GoType.PointerType storage.schema.authReadTx.ty, #l⟩ (backend.rtHeld dn.γB dn.P dn.be rtx rv))
    $$ [$Hpkg $Hinv $Hh $HGA] as Hh
  (try wp_auto)
  -- `tx.RUnlock()`: the reader's slot back to the pool
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (hRU dn.γB dn.P W Pk dn.be rt rtx rv) $$ [$Hbpkg $HB $Hrt $Hh] as Hr
  imod backend.rdTok_giveBack dn.γB dn.P dn.be ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hloan $Hr]
    with Htt
  (try wp_auto)
  -- `enabled` set to the value read, `false`
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$HenG] as ⟨Hlk, HP⟩
  iunfold auth.offEnP at HP
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HP]
  · inext; iunfold auth.offEnP; iexact HP
  (try wp_auto)
  iapply HΦ
  iframe Ho Htt Hrb
  isplitl [Hbe]
  · iunfold authBeOn
    iexists abl, lg
    iframe Hbe Habbe Hablg
    ipureintro; exact Hlg
  iunfold backend.bkRPool
  iframe Hrp Hrs

/-- **The disabled store's request side** (`isReqAuth`) at the reader resource `offRd`. -/
theorem isReqAuth_off (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (stl : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.offInv stl ⊢
      isReqAuth (auth.authIface stl) (auth.offRd stl) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isReqAuth
  iexists ⟨go.GoType.PointerType auth.authStore.ty, #stl⟩
  isplitr
  · ipureintro; rfl
  isplitl []
  · iintro !> %ctx %Φ !> ⟨-, -, Hrd⟩ HΦ
    iapply (auth.authInfoFromCtx_off stl (GoInterface.ok ctx)) $$ [$Hpkg $Hinv $Hrd]
    iintro !> %a %err ⟨Hrd, %Hae⟩
    obtain ⟨rfl, rfl⟩ := Hae
    iapply HΦ
    iframe Hrd
    isplitr
    · iunfold authInfoOpt; ileft; ipureintro; first | rfl | trivial
    iapply authApplyErrIs_nil
  · iintro !> %ctx %Φ !> ⟨#Hlib, -⟩ HΦ
    iunfold context.libCtxOk at Hlib
    icases Hlib with ⟨#Hinc, -, #Hpeer, -⟩
    iapply (hTLS stl iprop(True) .off ctx) $$ []
    · iframe #
    iintro !> %a #Ha
    iapply HΦ
    iapply authInfoRO_authInfoOpt a $$ Ha

/-- **The disabled store's apply contract** (`authApplyOk`) at the reader resource `offRd`: its
checks pass (`nil`), its flag `false`; its admin clauses vacuous (`apply.adminAdmitted`). -/
theorem authApplyOk_off (stl : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.offInv stl ⊢
      authApplyOk stl (auth.offRd stl) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold authApplyOk
  iintro !> %d %W %Pk %f %RW - - %_ -
  iunfold apply.isAuthStore
  iexists ⟨go.GoType.PointerType auth.authStore.ty, #stl⟩
  isplitr
  · ipureintro; rfl
  isplitl []
  · iunfold apply.permCheck2
    iintro !> %a %info %dq %key %k %dk %Φ !> ⟨Ha, Hk, Hrd, -⟩ HΦ
    iapply (auth.isPutPermitted_off stl a info dq key) $$ [$Hpkg $Hinv $Hrd $Ha]
    iintro !> %err ⟨Hrd, Ha, %Herr⟩
    subst Herr
    iapply HΦ
    iframe
    isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro; rfl
    simp only [auth.permVerdict]; ipureintro; first | rfl | trivial
  isplitl []
  · iunfold apply.permCheck3
    iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, -⟩ HΦ
    iapply (auth.isRangePermitted_off stl a info dq key re) $$ [$Hpkg $Hinv $Hrd $Ha]
    iintro !> %err ⟨Hrd, Ha, %Herr⟩
    subst Herr
    iapply HΦ
    iframe
    isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro; rfl
    simp only [auth.permVerdict]; ipureintro; first | rfl | trivial
  isplitl []
  · iunfold apply.permCheck3
    iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, -⟩ HΦ
    iapply (auth.isDeleteRangePermitted_off stl a info dq key re) $$ [$Hpkg $Hinv $Hrd $Ha]
    iintro !> %err ⟨Hrd, Ha, %Herr⟩
    subst Herr
    iapply HΦ
    iframe
    isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro; rfl
    simp only [auth.permVerdict]; ipureintro; first | rfl | trivial
  isplitl []
  · iintro !> %a %info %dq %Φ !> ⟨Ha, Hrd⟩ HΦ
    iapply (auth.isAdminPermitted_off stl a) $$ [$Hpkg $Hinv $Hrd]
    iintro !> %err ⟨Hrd, %Herr⟩
    subst Herr
    iapply HΦ
    iframe
    isplitl []
    · iapply applyErrIs_nil
    isplitl []
    · ipureintro; intro; rfl
    simp only [auth.adminVerdict]; ipureintro; first | rfl | trivial
  isplitl []
  · iintro !> %u %r %Φ !> %h
    exact absurd h (EtcdGrove.apply.adminAdmitted_none _)
  isplitl []
  · iintro !> %Φ !> Hrd HΦ
    iapply (auth.isAuthEnabled_off stl) $$ [$Hpkg $Hinv $Hrd]
    iintro !> %b ⟨Hrd, %Hb⟩
    iapply HΦ
    iframe Hrd
    simp only [auth.enabledVerdict]; ipureintro; exact Hb
  isplitl []
  · iintro !> %Φ !> - HΦ
    iapply (auth.revision_off stl) $$ [$Hpkg $Hinv]
    iintro !> %x -
    iapply HΦ
    simp only [auth.revisionVerdict]; itrivial
  isplitl []
  · iintro !> %B %Pre %Q %Post %Φ !> ⟨%h, -⟩
    exact absurd h (EtcdGrove.apply.adminAdmitted_none _)
  isplitl []
  · iintro !> %B %Pre %Q %Post %Φ !> ⟨%h, -⟩
    exact absurd h (EtcdGrove.apply.adminAdmitted_none _)
  isplitl []
  · iintro !> %ctx %name %pw %B %Pre %Q %Post %Φ !> ⟨%h, -⟩
    exact absurd h (EtcdGrove.apply.adminAdmitted_none _)
  isplitl []
  · iunfold apply.authReqContractN
    iintro !> %r %n %B %Pre %Q %Post %Φ !> ⟨%h, -⟩
    exact absurd h (EtcdGrove.apply.adminAdmitted_none _)
  iterate 5 (
    isplitl []
    · iunfold apply.authReqContract
      iintro !> %r %B %Pre %Q %Post %Φ !> ⟨%h, -⟩
      exact absurd h (EtcdGrove.apply.adminAdmitted_none _))
  isplitl []
  · iunfold apply.authReqContractN
    iintro !> %r %n %B %Pre %Q %Post %Φ !> ⟨%h, -⟩
    exact absurd h (EtcdGrove.apply.adminAdmitted_none _)
  iterate 6 (
    isplitl []
    · iunfold apply.authReqContract
      iintro !> %r %B %Pre %Q %Post %Φ !> ⟨%h, -⟩
      exact absurd h (EtcdGrove.apply.adminAdmitted_none _))
  iintro !> %Φ !> Hrd HΦ
  iapply (auth.isAdminPermitted_off stl null) $$ [$Hpkg $Hinv $Hrd]
  iintro !> %err ⟨Hrd, %Herr⟩
  subst Herr
  iapply HΦ
  iframe
  isplitl []
  · iapply applyErrIs_nil
  isplitl []
  · ipureintro; intro; rfl
  simp only [auth.adminVerdict]; ipureintro; first | rfl | trivial

/-- **The disabled store's `Close`** (`authCloseOk`). -/
theorem authCloseOk_off (stl : Loc) :
    auth.offInv (GF := GF) stl ⊢ authCloseOk stl := by
  iintro #Hinv
  iunfold authCloseOk
  iunfold authCloser
  iintro !> %Φ !> ⟨#Hpkg, -⟩ HΦ
  iapply (auth.close_off stl) $$ [$Hpkg $Hinv]
  iintro !> %err %Herr
  iapply HΦ
  iframe
  ipureintro; exact ⟨Herr, trivial⟩

end proof

end EtcdGrove
end Perennial
