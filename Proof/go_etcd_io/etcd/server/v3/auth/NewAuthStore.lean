/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean`: `auth.NewAuthStore(lg, be, tp, cost)`
with auth off, over schema's auth backend on the real backend. Lean-first (no Rocq counterpart); an
axiom at the trust boundary from unit N4 (2026-10-17) to the authstore-noax stage (2026-11-18,
`notes/decisions.md`, "authstore-noax"), which proves it.

The constructor's code over the backend's specs (schema's `CreateAuthBuckets`, `BatchTx`, the batch
transaction's `Lock`, reads, `UnsafeSaveAuthRevision`, `UnsafeGetAllUsers` on the empty users'
bucket, `Unlock`, `ForceCommit`); the store it returns is the disabled store (`auth.offInv`,
`auth/OffInv.lean`), whose request side, apply contract, `Recover` and `Close` are
`etcdserver/AuthOff.lean`'s.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.NewAuthStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthOff
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__setupMetricsReporter
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Int
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__CreateAuthBuckets
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Lock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeReadAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeReadAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeSaveAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeGetAllUsers
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeForEach

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 16384 in
theorem auth.NewAuthStore.wp_proof
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (hCAB : schema.authBackend.CreateAuthBuckets.spec (GF := GF) (hG := hG))
    (hBTx : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (hFCm : schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG))
    (hLock : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hUnlock : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (hREn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hSave : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (hGAU : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFEb : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock_idle.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hURr : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFEr : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hEnR : schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRevR : schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGAR : schema.authReadTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG)) :
    auth.NewAuthStore.spec (GF := GF) (hG := hG) := by
  intro lg ab tp cost abl d W Pk qo S r hS hA hU hR
  wp_start as ⟨#Hlgz, %Htp, %Hfit, %Hab, #Habbe, #Hablg, #HB, Ho, Hh, Hwb, Hrb, %Hr⟩
  irename Hpkg2 => Hspkg
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  subst Hab
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  -- the backend's parameters at the auth buckets (the real instance's)
  have hRBa : d.P.RB mvcc.authBI.name = true := by simp only [mvcc.KBReal.P]; decide
  have hRBu : d.P.RB mvcc.authUsersBI.name = true := by simp only [mvcc.KBReal.P]; decide
  have hRBr : d.P.RB mvcc.authRolesBI.name = true := by simp only [mvcc.KBReal.P]; decide
  have hHBa : d.P.HB mvcc.authBI.name = true := by simp only [mvcc.KBReal.P]; decide
  have hSBa : d.P.SB mvcc.authBI.name = false := by simp only [mvcc.KBReal.P]; decide
  have hhka : d.P.hk mvcc.authBI.name schema.authRevisionKey = false := by simp only [mvcc.KBReal.P, backend.BParams.hk]; decide
  have hSa : S mvcc.authBI.name := hS _ (Or.inl rfl)
  have hSu : S mvcc.authUsersBI.name := hS _ (Or.inr (Or.inl rfl))
  have hSr : S mvcc.authRolesBI.name := hS _ (Or.inr (Or.inr rfl))
  -- the four write-back tokens
  icases (ownToks_add 3 1 d.γB.wb).1 $$ Hwb with ⟨Hwb1, Hwb⟩
  icases (ownToks_add 2 1 d.γB.wb).1 $$ Hwb with ⟨Hwb2, Hwb⟩
  icases (ownToks_add 1 1 d.γB.wb).1 $$ Hwb with ⟨Hwb3, Hwb4⟩
  ihave Hwb1 : backend.wbTok d.γB $$ [Hwb1]
  · iunfold backend.wbTok; iexact Hwb1
  ihave Hwb2 : backend.wbTok d.γB $$ [Hwb2]
  · iunfold backend.wbTok; iexact Hwb2
  ihave Hwb3 : backend.wbTok d.γB $$ [Hwb3]
  · iunfold backend.wbTok; iexact Hwb3
  ihave Hwb4 : backend.wbTok d.γB $$ [Hwb4]
  · iunfold backend.wbTok; iexact Hwb4
  (try wp_auto)
  wp_if_destruct
  · exact absurd rfl Hlg
  (try wp_auto)
  -- the cost check: out of bounds, a warning and the default cost (two paths); else nothing
  wp_join iprop(∃ c : w64, bcryptCost_ptr ↦ c ∗ lg_ptr ↦ lg) with [bcryptCost lg] as ⟨%c, Hbc, Hlgp⟩
  · (try wp_auto)
    wp_apply h_Int as %f0 -
    wp_apply h_Int as %f1 -
    wp_apply h_Int as %f2 -
    (try wp_auto)
    wp_apply h_Int as %f3 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Warn
    · iexact Hlgz
    (try wp_auto)
    simp only [_root_.Perennial.golang_org.x.crypto.bcrypt.DefaultCost]
    (try wp_auto)
    wp_join_done
    try (iexists _; iframe)
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply h_Int as %f0 -
      wp_apply h_Int as %f1 -
      wp_apply h_Int as %f2 -
      (try wp_auto)
      wp_apply h_Int as %f3 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply h_Warn
      · iexact Hlgz
      (try wp_auto)
      simp only [_root_.Perennial.golang_org.x.crypto.bcrypt.DefaultCost]
      (try wp_auto)
      wp_join_done
      try (iexists _; iframe)
    · (try wp_auto)
      wp_join_done
      try (iexists _; iframe)
  -- `CreateAuthBuckets()`: the auth buckets present, the part idle
  wp_apply (hCAB abl d.γB d.P W Pk d.be qo S r (by
      intro bi hbi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbi
      rcases hbi with rfl | rfl | rfl
      · exact ⟨hA, hRBa, hSa⟩
      · exact ⟨hU, hRBu, hSu⟩
      · exact ⟨hR, hRBr, hSr⟩)) $$ [$Hspkg $Habbe $HB $Ho $Hwb1 $Hrb] as ⟨Ho, Hrb⟩
  (try wp_auto)
  -- `tx := be.BatchTx()`
  wp_apply (hBTx abl d.γB d.P W Pk d.be lg) $$ [$Hspkg $Habbe $Hablg $HB]
    as %tx ⟨%atl, %t, %Htx, #Htxf, #Htlg, #Ht⟩
  subst Htx
  (try wp_auto)
  -- `tx.Lock()`: `LockInsideApply` with the post-lock hook unset
  wp_apply (hLock atl d.γB d.P W Pk d.be t qo (DFrac.own (1 : Qp).half) func.nil iprop(True) Pk)
    $$ [$Hspkg $Htxf $HB $Ht $Ho $Hh] as ⟨%st, Hl, %Hfree, HW, HPk, Ho, Hh⟩
  · isplitr
    · itrivial
    ileft
    isplitr
    · ipureintro; rfl
    iintro ⟨H, -⟩; iexact H
  -- the writer's contents agree with the auth buckets' part
  ihave Hrb := backend.rbOwnIn_part _ _ _ $$ Hrb
  icases backend.batchLocked_rbPart d.γB d.P d.be st S _ $$ [$Hl $Hrb] with ⟨Hl, Hrb, %Hag⟩
  have hbkt : ∀ n, S n → d.P.RB n = true → st.S.lookup n = (schema.authCreated r).lookup n := by
    intro n hn hrb
    have h := Hag n hn
    rw [backend.rbData_lookup, hrb] at h
    simpa using h
  have hbA : backend.bktOf st.S mvcc.authBI.name = (r.lookup mvcc.authBI.name).getD ∅ := by
    unfold backend.bktOf; rw [hbkt _ hSa hRBa, schema.authCreated_auth]; rfl
  have hbU : backend.bktOf st.S mvcc.authUsersBI.name = ∅ := by
    unfold backend.bktOf; rw [hbkt _ hSu hRBu, schema.authCreated_users]; exact Hr.2.1
  -- the part of `Auth` apart (its write resource), the rest kept
  have hsplit : ∀ n, S n ↔ (n = mvcc.authBI.name ∨ (S n ∧ n ≠ mvcc.authBI.name)) := by
    intro n; by_cases hn : n = mvcc.authBI.name
    · subst hn; exact ⟨fun _ => Or.inl rfl, fun _ => hSa⟩
    · exact ⟨fun h => Or.inr ⟨h, hn⟩, fun h => h.elim (fun e => absurd e hn) And.left⟩
  ihave Hrb := (backend.rbPart_set d.γB S _ _ hsplit).1 $$ Hrb
  icases (backend.rbPart_split d.γB (· = mvcc.authBI.name) (fun n => S n ∧ n ≠ mvcc.authBI.name) _
    (fun n h1 h2 => h2.2 h1)).1 $$ Hrb with ⟨HrbA, HrbO⟩
  ihave HrbA : backend.rbPut d.γB d.P mvcc.authBI.name st.S $$ [HrbA]
  · unfold backend.rbPut; rw [hRBa]; simp only [↓reduceIte]
    iapply (backend.rbPart_congr d.γB _ _ _ (fun n hn => by
      subst hn; rw [backend.rbData_lookup, hRBa]; simp only [↓reduceIte]
      exact (hbkt _ hSa hRBa).symm)).1 $$ HrbA
  ihave #Hrd := schema.batch_authReader hUR hID hName hSafe d.γB d.P W Pk d.be t st
    $$ [$Hspkg $Hbpkg $HB $Ht]
  -- `UnsafeReadAuthEnabled()`: `false` (the auth bucket empty or at `authBoot`)
  have hA0 : (r.lookup mvcc.authBI.name).getD ∅ = ∅ ∨
      (r.lookup mvcc.authBI.name).getD ∅ = authBoot := Hr.1
  have hauthD : (schema.authDataOf st.S).auth = (r.lookup mvcc.authBI.name).getD ∅ := hbA
  have hen0 : schema.enabledOf (schema.authDataOf st.S) = false := by
    unfold schema.enabledOf
    rcases hA0 with h | h
    · simp [hauthD, h]
    · simp [hauthD, h, authBoot_enabled]
  wp_apply (hREn atl ⟨go.GoType.PointerType storage.backend.batchTxBuffered.ty, #t⟩
      (backend.batchLocked d.γB d.P d.be st) (schema.authDataOf st.S)) $$ [$Hspkg $Htxf $Hrd $Hl]
    as %enb ⟨Hl, %Henb⟩
  rw [hen0] at Henb
  subst Henb
  (try wp_auto)
  -- `UnsafeReadAuthRevision()`: `0` (empty) or `1` (`authBoot`)
  have hrw : schema.revWf (schema.authDataOf st.S).auth := by
    rw [hauthD]
    rcases hA0 with h | h <;> rw [h]
    · intro v hv; cases hv
    · exact authBoot_revWf
  wp_apply (hRRev atl ⟨go.GoType.PointerType storage.backend.batchTxBuffered.ty, #t⟩
      (backend.batchLocked d.γB d.P d.be st) (schema.authDataOf st.S) hrw) $$ [$Hspkg $Htxf $Hrd $Hl]
    as %x ⟨Hl, %Hx⟩
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
    (go.GoType.PointerType auth.unifiedRangePermissions.ty)) as %mp HM
  (try wp_auto)
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hst, %Hstnn⟩
  iStructNamed Hst
  (try wp_auto)
  icases backend.isBackend_b d.γB d.P W Pk d.be $$ HB with ⟨%t', %rt, %db, %lg', -, -, -, -, -, -, -,
    -, -, -, -, %HPw⟩
  have hvs0 : backend.viewSame d.P st := backend.viewSame_of_freeOk Hfree
  have hp0 := Hfree.2.1
  have hlim := HPw.2.2.1
  -- `if as.Revision() == 0 { as.commitRevision(tx) }`: the auth bucket at `authBoot` after, the
  -- revision `1`
  wp_apply (auth.revision_own «$r0_ptr» x) $$ [$Hpkg $revision] as revision
  wp_join iprop(∃ st' : backend.BSess, tx_ptr ↦ (interface.mkOk
        (go.GoType.PointerType storage.schema.authBatchTx.ty) #atl : GoInterface) ∗
      as_ptr ↦ «$r0_ptr» ∗ auth.aF go!"revision" «$r0_ptr» ↦ W64 1 ∗
      backend.batchLocked d.γB d.P d.be st' ∗ backend.rbPut d.γB d.P mvcc.authBI.name st'.S ∗
      ⌜st'.S.lookup mvcc.authBI.name = some authBoot ∧
        (∀ n, n ≠ mvcc.authBI.name → st'.S.lookup n = st.S.lookup n) ∧ st'.cnt = st.cnt ∧
        backend.viewSame d.P st' ∧ sint.Z st'.pend ≤ sint.Z st.pend + 1⌝)
    with [tx «as» revision Hl HrbA] as ⟨%st', tx, «as», revision, Hl, HrbA, %Hst'⟩
  · -- revision `0`: the bucket empty; `authRevision` put at `1`
    have hemp : (r.lookup mvcc.authBI.name).getD ∅ = ∅ := by
      rcases hA0 with h | h
      · exact h
      · exfalso
        have : schema.revisionOf (schema.authDataOf st.S) = W64 1 := by
          unfold schema.revisionOf
          rw [hauthD, h]; unfold authBoot schema.authRevisionKey
          rw [GMap.lookup_insert]; exact beToU64_u64Be _
        rw [← Hx] at this; exact absurd this (by decide)
    (try wp_auto)
    wp_apply (auth.commitRevision_own «$r0_ptr» (W64 0)
        ⟨go.GoType.PointerType storage.schema.authBatchTx.ty, #atl⟩
        iprop(backend.batchLocked d.γB d.P d.be st ∗ backend.rbPut d.γB d.P mvcc.authBI.name st.S)
        iprop(backend.batchLocked d.γB d.P d.be
            (st.put mvcc.authBI schema.authRevisionKey (u64Be (W64 0 + W64 1)) false) ∗
          backend.rbPut d.γB d.P mvcc.authBI.name
            (st.put mvcc.authBI schema.authRevisionKey (u64Be (W64 0 + W64 1)) false).S))
      $$ [$Hpkg $revision Hl HrbA] as ⟨revision, HP⟩
    · iframe Hl HrbA
      iunfold auth.saveRevOk
      iintro %Φ' !> ⟨Hl, HrbA⟩ HΦ'
      iapply (hSave atl d.γB d.P W Pk d.be t st (W64 0 + W64 1) hA hSBa hhka (by omega))
        $$ [$Hspkg $Htxf $HB $Ht $Hl $HrbA]
      iexact HΦ'
    rw [show W64 0 + W64 1 = W64 1 from rfl]
    icases HP with ⟨Hl, HrbA⟩
    (try wp_join_done)
    iexists (st.put mvcc.authBI schema.authRevisionKey (u64Be (W64 1)) false)
    iframe tx «as» revision
    isplitl [Hl]
    · iExactEq Hl; rfl
    isplitl [HrbA]
    · iExactEq HrbA; rfl
    ipureintro
    refine ⟨?_, ?_, rfl, mvcc.viewSame_putHB HPw hHBa hA hvs0, ?_⟩
    · show (st.S.insert mvcc.authBI.name _).lookup mvcc.authBI.name = _
      rw [GMap.lookup_insert]
      show some ((backend.bktOf st.S mvcc.authBI.name).insert _ _) = _
      rw [hbA, hemp]; rfl
    · intro n hn
      show (st.S.insert mvcc.authBI.name _).lookup n = _
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hn)]
    · show sint.Z (st.pend + W64 1) ≤ _
      word
  · -- revision `1`: the bucket at `authBoot`, nothing written
    have hx0 : x ≠ W64 0 := Hif
    have hboot : (r.lookup mvcc.authBI.name).getD ∅ = authBoot := by
      rcases hA0 with h | h
      · exfalso; apply hx0
        rw [Hx]; unfold schema.revisionOf
        rw [hauthD, h]; rfl
      · exact h
    have hx1 : x = W64 1 := by
      rw [Hx]; unfold schema.revisionOf
      rw [hauthD, hboot]; unfold authBoot schema.authRevisionKey
      rw [GMap.lookup_insert]; exact beToU64_u64Be _
    (try wp_auto)
    (try wp_join_done)
    iexists st
    iframe tx «as» Hl HrbA
    isplitl [revision]
    · rw [hx1]; iexact revision
    ipureintro
    exact ⟨by rw [hbkt _ hSa hRBa, schema.authCreated_auth, hboot], fun _ _ => rfl, rfl, hvs0,
      by omega⟩
  obtain ⟨hlk', hoth', hcnt', hvs', hpend'⟩ := Hst'
  -- `setupMetricsReporter()`
  wp_apply (h_metrics «$r0_ptr») $$ [$Hpkg]
  (try wp_auto)
  -- the disabled store's invariant: the revision's atomic, the three locks
  imod inv_alloc (nroot.@"authRev") ⊤ (∃ rv : w64, auth.aF go!"revision" «$r0_ptr» ↦ rv)
    $$ [revision] with #Hrev
  · inext; iexists _; iexact revision
  ihave ⟨Hbe1, Hbe2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ be
  imod (sync.init_RWMutex (auth.offBeP «$r0_ptr») (auth.aF go!"beMu" «$r0_ptr») (E := ⊤))
    $$ [Hbe1] beMu with HbeS
  · inext; iunfold auth.offBeP; iexists _; iexact Hbe1
  imod (sync.init_RWMutex (auth.offEnP «$r0_ptr») (auth.aF go!"enabledMu" «$r0_ptr») (E := ⊤))
    $$ [enabled] enabledMu with HenS
  · inext; iunfold auth.offEnP; iexact enabled
  imod (sync.init_RWMutex (auth.offCaP «$r0_ptr») (auth.aF go!"rangePermCacheMu" «$r0_ptr»)
    (E := ⊤)) $$ [rangePermCache] rangePermCacheMu with HcaS
  · inext; iunfold auth.offCaP; iexists mp; iexact rangePermCache
  ihave ⟨-, #Gbe⟩ := sync.ownRWMutex_slots_guard _ _ $$ HbeS
  ihave ⟨HenS, #Gen⟩ := sync.ownRWMutex_slots_guard _ _ $$ HenS
  ihave ⟨-, #Gca⟩ := sync.ownRWMutex_slots_guard _ _ $$ HcaS
  ipersist lg
  ihave #Hinv : auth.offInv «$r0_ptr» $$ []
  · iunfold auth.offInv
    iframe Hrev Gbe Gen Gca
    isplitr
    · ipureintro; exact Hstnn
    iexists lg; iframe lg Hlgz
  -- `refreshRangePermCache(tx)`: no user
  have hbU' : backend.bktOf st'.S mvcc.authUsersBI.name = ∅ := by
    unfold backend.bktOf; rw [hoth' _ (by decide)]; exact hbU
  ihave #HFE := schema.batch_forEachUsersEmpty hFEb hID hName hSafe d.γB d.P W Pk d.be t st' hU hbU'
    $$ [$Hspkg $Hbpkg $HB $Ht]
  ihave #HGA : auth.getAllUsersNone ⟨go.GoType.PointerType storage.schema.authBatchTx.ty, #atl⟩
      (backend.batchLocked d.γB d.P d.be st') $$ []
  · iunfold auth.getAllUsersNone
    iintro !> %Φ' !> HH HΦ'
    iapply (hGAU atl lg ⟨go.GoType.PointerType storage.backend.batchTxBuffered.ty, #t⟩
      (backend.batchLocked d.γB d.P d.be st')) $$ [$Hspkg $Htxf $Htlg $HH $HFE]
    iexact HΦ'
  wp_apply (auth.refreshRangePermCache_off h_Debug «$r0_ptr»
      ⟨go.GoType.PointerType storage.schema.authBatchTx.ty, #atl⟩ (backend.batchLocked d.γB d.P d.be st'))
    $$ [$Hpkg $Hinv $Hl $HGA] as Hl
  (try wp_auto)
  -- `tx.Unlock()`: the auth buckets' part idle, at `authBoot`
  have hfin : ∀ n, n = mvcc.authBI.name →
      (backend.rbData d.P st'.S).lookup n = ((schema.authCreated r).insert mvcc.authBI.name authBoot).lookup n := by
    rintro n rfl
    rw [backend.rbData_lookup, hRBa, GMap.lookup_insert]
    simpa using hlk'
  ihave HrbA : backend.rbPart d.γB (· = mvcc.authBI.name)
      ((schema.authCreated r).insert mvcc.authBI.name authBoot) $$ [HrbA]
  · unfold backend.rbPut; rw [hRBa]; simp only [↓reduceIte]
    iapply (backend.rbPart_congr d.γB _ _ _ hfin).1 $$ HrbA
  ihave HrbO := (backend.rbPart_congr d.γB _ (schema.authCreated r)
    ((schema.authCreated r).insert mvcc.authBI.name authBoot)
    (fun n hn => by rw [GMap.lookup_insert_ne _ _ (Ne.symm hn.2)])).1 $$ HrbO
  ihave Hrb := (backend.rbPart_split d.γB (· = mvcc.authBI.name) (fun n => S n ∧ n ≠ mvcc.authBI.name) _
    (fun n h1 h2 => h2.2 h1)).2 $$ [$HrbA $HrbO]
  ihave Hrb := (backend.rbPart_set d.γB S _ _ hsplit).2 $$ Hrb
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin d.γB d.P _ hvs'
  ihave #Hcr := backend.commitReq_true (GF := GF) d.γB d.P Pk d.be
  have hhw : st'.cnt.hw = false := by rw [hcnt']; exact Hfree.2.2.2.2
  have hroom : sint.Z st'.pend + d.P.hookMax < 2 ^ 58 := by
    have := HPw.2.2.2.1; omega
  wp_apply (hUnlock atl d.γB d.P W Pk d.be t st' iprop(True) S
      ((schema.authCreated r).insert mvcc.authBI.name authBoot) qo iprop(True) iprop(True) hhw hroom)
    $$ [$Hspkg $Htxf $HB $Ht $Hl $Hwb2 $Hrb HW HPk $Hwb3 $Ho $Hcr] as ⟨-, Hrb, Ho, -⟩
  · ileft; iframe HW HPk Hth; ipureintro; exact Hnw
  (try wp_auto)
  -- `be.ForceCommit()`
  wp_apply (hFCm abl d.γB d.P W Pk d.be qo iprop(True) iprop(True)) $$ [$Hspkg $Habbe $HB $Ho $Hwb4 $Hcr]
    as ⟨Ho, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Ho Hh
  isplitl [Hrb]
  · iapply (backend.rbOwnIn_congr d.γB S
      ((schema.authCreated r).insert go_etcd_io.etcd.server.v3.storage.schema.authName authBoot)
      (((r.insert go!"auth" authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅)
      (fun n _ => by exact schema.authCreated_final r authBoot Hr.2.1 Hr.2.2 n)).1 $$ Hrb
  iexists (auth.offRd «$r0_ptr»), «$r0_ptr»
  isplitr
  · ipureintro; rfl
  isplitl [Hbe2]
  · iunfold authBeOn
    iexists abl, lg
    iframe Hbe2 Habbe Hablg
    ipureintro; exact Hlg
  isplitl [HenS]
  · iunfold auth.offRd; iexact HenS
  isplitl []
  · iapply (isReqAuth_off hTLS «$r0_ptr») $$ [$Hpkg $Hinv]
  isplitl []
  · iapply (authApplyOk_off «$r0_ptr») $$ [$Hpkg $Hinv]
  isplitl []
  · iapply (authRecoverOk_off hRT hRL hRU hURr hFEr hID hName hSafe hEnR hRevR hGAR h_Debug «$r0_ptr»)
      $$ [$Hpkg $Hspkg $Hinv]
  iapply (authCloseOk_off «$r0_ptr») $$ Hinv

end proof

end EtcdGrove
end Perennial
