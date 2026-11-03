/-
**`NewAuthStore` over its backend's and token provider's contracts, in the mode `on γa`** (the
auth plan's E2a, 2026-10-25; `notes/decisions.md`, "E2a of the auth plan"). Lean-first (no Rocq
counterpart).

`auth.NewAuthStore.spec` (`Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean`) is the
server's statement: over schema's real auth backend on the real backend (its tracked buckets,
`backend.rbOwn`, D22), in the mode `off`, with the apply package's contract on every backend
(`authApplyOk`); it stays an axiom (what is missing: schema's auth write side over the backend's
tracked buckets, D22; and the admin clauses `isAuthStoreAdmin` of the store: `HasRole`,
`Authenticate`, `UserGet`, `RoleGet` and the lists). `newAuthStore_on` is the constructor's own
code, proved: `NewAuthStore(lg, be, tp, cost)` on an `AuthBackend` `be` meeting the store's backend
contracts (`authBackendOk`, the read side; `authWBackendOk`, the write side, S4; and
`CreateAuthBuckets`, one transaction), a token provider meeting its contract with its admin
resource (`tokenProviderOkA`, S5d), and the admin side's authority at a history `hs` (both halves of
its latest state's ghost variable), returns a store whose invariant (`authInv`) holds in the mode
`on γa`, with the admin side's write resource (`authWR`), the provider's share (`tpAdmin`), the
authority (grown by the revision's commit when the backend's state had revision `0`), and the
readers' slots of its three locks.

**The initial permission cache.** `NewAuthStore` makes the cache's map empty and refreshes it from
the transaction only after `Revision()` and `commitRevision`, which (with `refreshRangePermCache`)
take the store's invariant: the cache's lock is made with the empty map, which the invariant's
`cacheOk` (on) accepts only as the map of a recorded state with no users (no reader can observe
it: the store is not shared yet). Hence the premise that the history has such a state: the
history of a store whose buckets were created empty starts with one (the empty state).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__setupMetricsReporter
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Int

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section ghost
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- The authority keeps a recorded state. -/
theorem authOwnF_stateAt_keep (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState)
    (h : hs[i]? = some st) :
    authOwnF (GF := GF) (.on γa) hs ⊢ |==> (authOwnF (.on γa) hs ∗ authStateAt γa i st) := by
  simp only [authOwnF]
  iintro ⟨Hh, Hc⟩
  imod (authHist_stateAt_keep γa hs i st h) $$ Hh with ⟨Hh, #H⟩
  imodintro
  isplitl [Hh Hc]
  · iframe Hh Hc
  · iexact H

end ghost

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem Qp.half_add (p q : Qp) : (p + q).half = p.half + q.half := Subtype.ext (by grind)

/-- `enabledMu`'s invariant is fractional (for `sync.init_RWMutex`). -/
instance enabledP_fractional (st : Loc) (M : AuthMode) :
    Fractional (enabledP (GF := GF) st M) := by
  unfold enabledP
  exact fractional_exists_agree
    (fun (b : Bool) q => iprop(aF go!"enabled" st ↦{DFrac.own q.half} b ∗ enabledVerdict M b ∗
      enG M q.half b))
    (fun b => ⟨fun q1 q2 => by
      rw [Qp.half_add]
      constructor
      · iintro ⟨H, #Hv, Hg⟩
        icases (typedPointsto_frac_add _ _ q1.half q2.half).1 $$ H with ⟨H1, H2⟩
        icases (enG_split M q1.half q2.half b).1 $$ Hg with ⟨Hg1, Hg2⟩
        iframe H1 H2 Hv Hg1 Hg2
      · iintro ⟨⟨H1, #Hv, Hg1⟩, ⟨H2, -, Hg2⟩⟩
        iframe Hv
        isplitl [H1 H2]
        · iapply (typedPointsto_frac_add _ _ q1.half q2.half).2 $$ [$H1 $H2]
        · iapply (enG_split M q1.half q2.half b).2 $$ [$Hg1 $Hg2]⟩)
    (fun x y q1 q2 => by
      iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
      icombine H1 H2 gives %Heq
      ipureintro; exact Heq)

/-- `beMu`'s invariant is fractional. -/
instance beP_fractional (st : Loc) (R : IProp GF) (M : AuthMode) :
    Fractional (beP (GF := GF) st R M) := by
  unfold beP
  exact fractional_exists_agree
    (fun (be : AuthBackend) q => iprop(aF go!"be" st ↦{DFrac.own q.half} be ∗ authBackendOk be R M))
    (fun b => ⟨fun q1 q2 => by
      rw [Qp.half_add]
      constructor
      · iintro ⟨H, #Hv⟩
        icases (typedPointsto_frac_add _ _ q1.half q2.half).1 $$ H with ⟨H1, H2⟩
        iframe H1 H2 Hv
      · iintro ⟨⟨H1, #Hv⟩, ⟨H2, -⟩⟩
        iframe Hv
        iapply (typedPointsto_frac_add _ _ q1.half q2.half).2 $$ [$H1 $H2]⟩)
    (fun x y q1 q2 => by
      iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
      icombine H1 H2 gives %Heq
      ipureintro; exact Heq)

/-- `rangePermCacheMu`'s invariant is fractional. -/
instance cacheP_fractional (st : Loc) (M : AuthMode) :
    Fractional (cacheP (GF := GF) st M) := by
  unfold cacheP
  exact fractional_exists_agree
    (fun (mp : GoMap) q => iprop(∃ Mp : GMap GoString Loc,
      aF go!"rangePermCache" st ↦{DFrac.own q.half} mp ∗ mp ↦${DFrac.discard} Mp ∗ cacheOk M Mp ∗
        caGM M q.half mp Mp))
    (fun mp => fractional_exists_agree
      (fun (Mp : GMap GoString Loc) q => iprop(aF go!"rangePermCache" st ↦{DFrac.own q.half} mp ∗
        mp ↦${DFrac.discard} Mp ∗ cacheOk M Mp ∗ caGM M q.half mp Mp))
      (fun Mp => ⟨fun q1 q2 => by
        rw [Qp.half_add]
        constructor
        · iintro ⟨H, #Hm, #Hv, Hg⟩
          icases (typedPointsto_frac_add _ _ q1.half q2.half).1 $$ H with ⟨H1, H2⟩
          icases (caGM_split M q1.half q2.half mp Mp).1 $$ Hg with ⟨Hg1, Hg2⟩
          iframe H1 H2 Hm Hv Hg1 Hg2
        · iintro ⟨⟨H1, #Hm, #Hv, Hg1⟩, ⟨H2, -, -, Hg2⟩⟩
          iframe Hm Hv
          isplitl [H1 H2]
          · iapply (typedPointsto_frac_add _ _ q1.half q2.half).2 $$ [$H1 $H2]
          · iapply (caGM_split M q1.half q2.half mp Mp).2 $$ [$Hg1 $Hg2]⟩)
      (fun x y q1 q2 => by
        iintro ⟨⟨-, H1, -⟩, ⟨-, H2, -⟩⟩
        iapply ownMap_agree $$ [$H1 $H2]))
    (fun x y q1 q2 => by
      iintro ⟨⟨%M1, H1, -⟩, ⟨%M2, H2, -⟩⟩
      icombine H1 H2 gives %Heq
      ipureintro; exact Heq)

/-- The three locks' slot lists as one list of a slot of each (`n` abstract: the readers' bound
`2 ^ 30 - 1` is never unfolded, which the kernel would otherwise do). -/
theorem slots_rd (n : Nat) (st : Loc) (R : IProp GF) (M : AuthMode) :
    ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (aF go!"enabledMu" st) (enabledP st M)) ∗
      ([∗list] _x ∈ List.replicate n (),
        sync.ownRWMutex (aF go!"rangePermCacheMu" st) (cacheP st M)) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (aF go!"beMu" st) (beP st R M)) ⊢
    [∗list] _x ∈ List.replicate n (), enabledRd st M ∗ cacheRd st M ∗ beRd st R M := by
  unfold enabledRd cacheRd beRd
  iintro ⟨H1, H2, H3⟩
  iapply BigSepL.bigSepL_sep_eqv.2
  iframe H1
  iapply BigSepL.bigSepL_sep_eqv.2
  iframe H2 H3

/-- **The admin side's write resource at the backend `be` the store's field holds** (the auth
plan's E2i, 2026-10-26: `newAuthStore_on`'s post, so that the server's `authBeOn` can name the
backend; `authWR` forgets it, `authWRAt_authWR`). -/
def authWRAt (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (be : AuthBackend) : IProp GF :=
  iprop((aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗ authWBackendOk be M P f T) ∗ T ∗
    enabledHalf st M ∗ cacheHalf st M)

theorem authWRAt_authWR (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (be : AuthBackend) : authWRAt (GF := GF) st M P f T be ⊢ authWR st M P f T := by
  iintro H
  iunfold authWRAt at H
  icases H with ⟨⟨Hbe, #Hok⟩, HT, Hen, Hca⟩
  iunfold authWR
  iframe HT Hen Hca
  iexists be
  iframe Hbe Hok

/-- The provider's contract with its admin resource gives the invariant's. -/
theorem tokenProviderOk_of_A (tp : GoInterface) (M : AuthMode) (A : IProp GF) :
    tokenProviderOkA (GF := GF) tp M A ⊢ tokenProviderOk tp M := by
  unfold tokenProviderOkA tokenProviderOk
  iintro ⟨%ti, %Hti, #H1, #H2, #H3, #H4, #H5, #H6⟩
  iexists A, ti
  iframe #
  ipureintro; exact Hti

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

set_option maxRecDepth 16384 in
/-- **`NewAuthStore(lg, be, tp, cost)` in the mode `on γa`** (see the file header). -/
theorem newAuthStore_on
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (lg : Loc) (ab tp : GoInterface) (cost : w64) (bi : GoInterfaceOk) (γa : AuthNames)
    (R P : IProp GF) (f : val) (T A Pre Q Post : IProp GF) (hs : List AuthState)
    (stl : AuthState) (hlast : hs.getLast? = some stl) (hfit : permsFit stl)
    (hempty : ∃ s ∈ hs, s.users = ∅) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
        ⌜ab = GoInterface.ok bi⌝ ∗ authBackendOk ab R (.on γa) ∗
        authWBackendOkR ab (.on γa) P f T ∗
        □ ({{ T }} (App (Val #(methods bi.ty go!"CreateAuthBuckets" bi.v)) (Val #()))
          {{ RET #(); T }}) ∗
        T ∗ mvcc.csContract P f Pre Q Post ∗ tokenProviderOkA tp (.on γa) A ∗ A ∗
        authOwn (.on γa) hs ∗ authStoreInit γa hs stl ∗ capNext (.on γa) hs (bump stl) }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; ∃ (stp : Loc) (hs' : List AuthState),
        ⌜st = authIface stp⌝ ∗ authInv stp R (.on γa) ∗ authWRAt stp (.on γa) P f T ab ∗
        tpAdmin stp (.on γa) ∗ Post ∗ authOwn (.on γa) hs' ∗
        ⌜(stl.revision ≠ 0 ∧ hs' = hs) ∨ (stl.revision = 0 ∧ hs' = hs ++ [bump stl])⌝ ∗
        -- (authkv's Main, 2026-10-30) the cost field, read-only (`BcryptCost()`'s)
        (∃ c : w64, aF go!"bcryptCost" stp ↦□ c) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          enabledRd stp (.on γa) ∗ cacheRd stp (.on γa) ∗ beRd stp R (.on γa)) }} := by
  wp_start as ⟨%Hlg, %Hab, #Hrdok, #HwokR, #HCreate, HT, Hcs, #HtpA, HA, Hown, Hcur, #Hcn⟩
  iunfold authStoreInit at Hcur
  icases Hcur with ⟨Hcur, Hrq, #Hcl, Hpub, ⟨%b0, Hfe⟩, %v0, Hfc⟩
  ihave #Hwok := authWBackendOk_of_R _ (.on γa) P f T $$ HwokR
  subst Hab
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hwok' := Hwok
  iunfold authWBackendOk at Hwok'
  icases Hwok' with ⟨%bi', %Hbi', #HBatch, #HFC, -⟩
  cases Hbi'
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
    · ipureintro; exact Hlg
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
      · ipureintro; exact Hlg
      (try wp_auto)
      simp only [_root_.Perennial.golang_org.x.crypto.bcrypt.DefaultCost]
      (try wp_auto)
      wp_join_done
      try (iexists _; iframe)
    · (try wp_auto)
      wp_join_done
      try (iexists _; iframe)
  -- `CreateAuthBuckets()`, one transaction
  wp_bind (App (Val #(methods bi.ty go!"CreateAuthBuckets" bi.v)) (Val #()))
  iapply HCreate $$ HT
  inext
  iintro HT
  (try wp_auto)
  -- `tx := be.BatchTx()`, locked: the latest state
  wp_apply HBatch as %tx Htx
  iunfold authBatchTxOk at Htx
  icases Htx with ⟨%ti, %Hti, %Lk, #HLk⟩
  subst Hti
  ihave #HLk' := HLk
  iunfold authBatchTxLk at HLk'
  icases HLk' with ⟨#HLock, #HRd, -, -, -, -, -, -, #HUnlock, -, -⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"Lock" ti.v)) (Val #()))
  iapply HLock $$ %hs %Pre %Q %Post [$Hcs $HT $Hown]
  inext
  iintro ⟨%st0, HL, Hown, %Hl0⟩
  have Hst0 : st0 = stl := by
    simp only [histLast] at Hl0; rw [hlast] at Hl0; cases Hl0; rfl
  subst Hst0
  ihave #HRd' := HRd $$ %Post
  iunfold authReaderOk at HRd'
  icases HRd' with ⟨#HUG, #HUR, #HRE, #HRR, #HAll⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeReadAuthEnabled" ti.v)) (Val #()))
  iapply HRE $$ %st0 HL
  inext
  iintro %b ⟨HL, %Hb⟩
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeReadAuthRevision" ti.v)) (Val #()))
  iapply HRR $$ %st0 HL
  inext
  iintro %x ⟨HL, %Hx⟩
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
    (go.GoType.PointerType unifiedRangePermissions.ty)) as %mp HM
  (try wp_auto)
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hst, %Hstnn⟩
  iStructNamed Hst
  -- the latest state and an empty one are recorded
  have hidx : hs[hs.length - 1]? = some st0 := by rw [← List.getLast?_eq_getElem?]; exact hlast
  imod (authOwnF_stateAt_keep γa hs _ st0 hidx) $$ Hown with ⟨Hown, #Hst0⟩
  obtain ⟨se, hse, hseu⟩ := hempty
  obtain ⟨ie, hie⟩ := List.mem_iff_getElem?.1 hse
  imod (authOwnF_stateAt_keep γa hs ie se hie) $$ Hown with ⟨Hown, #Hse⟩
  obtain ⟨s0, hs0⟩ : ∃ s0, hs[0]? = some s0 := by
    cases hs with
    | nil => cases hlast
    | cons x xs => exact ⟨x, rfl⟩
  imod (authOwnF_stateAt_keep γa hs 0 s0 hs0) $$ Hown with ⟨Hown, #Hs0⟩
  -- the three locks' guards
  ihave ⟨Hbe1, Hbe2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ be
  ihave ⟨Hen1, Hen2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ enabled
  imod (sync.init_RWMutex (beP «$r0_ptr» R (.on γa)) (aF go!"beMu" «$r0_ptr») (E := ⊤))
    $$ [Hbe1] beMu with HbeS
  · inext; iunfold beP; iexists _; iframe Hbe1; iexact Hrdok
  -- (E3h) the field's ghost variable at the flag read: half the guard's, a quarter the admin
  -- side's, a quarter the store's freshness
  imod (ghostVar_update b γa.fen b0) $$ Hfe with Hfe
  icases (ghostVar_split_half γa.fen 1 b).1 $$ Hfe with ⟨HfeG, Hfe2⟩
  icases (ghostVar_split_half γa.fen (1 : Qp).half b).1 $$ Hfe2 with ⟨HfeA, HfeI⟩
  imod (sync.init_RWMutex (enabledP «$r0_ptr» (.on γa)) (aF go!"enabledMu" «$r0_ptr») (E := ⊤))
    $$ [Hen1 HfeG] enabledMu with HenS
  · inext; iunfold enabledP; iexists _; iframe Hen1
    isplitl []
    · iunfold enabledVerdict; iexists _, st0; iframe Hst0; ipureintro; exact Hb
    · iunfold enG; iexact HfeG
  ihave ⟨Hca1, Hca2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ rangePermCache
  imod ownMap_persist mp _ ∅ $$ HM with #HM
  ihave #Hof : (cacheOf (GF := GF) se ∅) $$ []
  · iunfold cacheOf
    isplitr
    · ipureintro; intro u; simp [hseu]
    · iapply BigSepM.bigSepM_empty.2; itrivial
  -- (E3h) the cache's ghost variable at the empty map of the empty state: half the guard's, a
  -- quarter the admin side's, a quarter the store's freshness
  imod (ghostVar_update (mp, ie) γa.fca v0) $$ Hfc with Hfc
  icases (ghostVar_split_half γa.fca 1 (mp, ie)).1 $$ Hfc with ⟨HfcG, Hfc2⟩
  icases (ghostVar_split_half γa.fca (1 : Qp).half (mp, ie)).1 $$ Hfc2 with ⟨HfcA, HfcI⟩
  imod (sync.init_RWMutex (cacheP «$r0_ptr» (.on γa)) (aF go!"rangePermCacheMu" «$r0_ptr»)
    (E := ⊤)) $$ [Hca1 HfcG] rangePermCacheMu with HcaS
  · inext; iunfold cacheP; iexists mp, ∅; iframe Hca1 HM
    isplitl []
    · iunfold cacheOk; iexists ie, se; iframe Hse
      isplitr
      · ipureintro; intro u; simp [hseu]
      · iapply BigSepM.bigSepM_empty.2; itrivial
    iunfold caGM; iexists ie, se; iframe HfcG Hse Hof
  ihave Hca : (cacheHalf (GF := GF) «$r0_ptr» (.on γa)) $$ [Hca2 HfcA]
  · iunfold cacheHalf; iexists se
    isplitl [Hca2 HfcA]
    · iunfold cacheAt; iexists mp, ∅; iframe Hca2 HM Hof
      iunfold caA; iexists ie, se; iframe HfcA Hse; ipureintro; rfl
    · iunfold authSnap; iexists ie; iexact Hse
  ihave ⟨HbeS, #Gbe⟩ := sync.ownRWMutex_slots_guard _ _ $$ HbeS
  ihave ⟨HenS, #Gen⟩ := sync.ownRWMutex_slots_guard _ _ $$ HenS
  ihave ⟨HcaS, #Gca⟩ := sync.ownRWMutex_slots_guard _ _ $$ HcaS
  ipersist lg
  ipersist tokenProvider
  ipersist bcryptCost
  -- the revision's invariant
  imod inv_alloc (nroot.@"authRev") ⊤ (revInv (GF := GF) «$r0_ptr» (.on γa)) $$ [revision Hcur Hrq Hpub HfeI HfcI]
    with #Hrev
  · inext; iunfold revInv; iexists x; iframe revision
    isplitl []
    · iunfold revisionVerdict; iexists _, st0; iframe Hst0; ipureintro; exact Hx
    isplitl [Hcur Hrq]
    · iunfold revCur; iexists st0; iframe Hcur; isplitr
      · ipureintro; exact Hx
      · iexists hs; iframe Hrq Hcl
    · -- (E3h) nothing published yet: the published index `0`, the latest state's revision
      iunfold revFresh
      iexists 0
      iframe Hpub
      isplitl []
      · iexists s0; iexact Hs0
      isplitl []
      · iexists _, st0; iframe Hst0; ipureintro; exact ⟨Nat.zero_le _, Hx⟩
      isplitl [HfeI]
      · iexists b
        iframe HfeI
        iexists _, st0; iframe Hst0; ipureintro; exact ⟨Nat.zero_le _, Hb⟩
      iexists (mp, ie)
      iframe HfcI
      iexists se, ie, se; iframe Hse; ipureintro; exact ⟨Nat.zero_le _, rfl⟩
  ihave #Hinv : authInv (GF := GF) «$r0_ptr» R (.on γa) $$ []
  · iunfold authInv
    iframe Hrev Gbe Gen Gca
    isplitr
    · ipureintro; exact Hstnn
    isplitr
    · iexists lg; iframe lg; ipureintro; exact Hlg
    iexists tp; iframe tokenProvider
    iapply tokenProviderOk_of_A $$ HtpA
  -- `if enabled { as.tokenProvider.enable() }`: the provider's admin resource kept
  ihave #HtpA' := HtpA
  iunfold tokenProviderOkA at HtpA'
  icases HtpA' with ⟨%tpi, %Htpi, -, #HEnable, -, -, -, -⟩
  subst Htpi
  (try wp_auto)
  wp_join with [HA «as»]
  · (try wp_auto)
    wp_bind (App (Val #(methods tpi.ty go!"enable" tpi.v)) (Val #()))
    iapply HEnable $$ HA
    inext
    iintro HA
    (try wp_auto)
    wp_join_done
  -- `if as.Revision() == 0 { as.commitRevision(tx) }`: the latest state's revision
  ihave %Hpk := authOwnF_last_permKeysOk (.on γa) hs $$ Hown
  icases (authOwnF_split (.on γa) hs).1 $$ Hown with ⟨Hown, Hsh⟩
  wp_apply (h_Revision «$r0_ptr» R (.on γa) (some hs)) $$ [Hown] as %xr ⟨Hown, -, %Hxr⟩
  · iframe #; simp only [authOwnOpt_some]; iexact Hown
  iunfold authOwnOpt at Hown
  ihave Hown := (authOwnF_split (.on γa) hs).2 $$ [Hown Hsh]
  · iframe Hown Hsh
  have hxr : uint.nat xr = st0.revision := Hxr hs st0 rfl Hl0 rfl (by simp)
  (try wp_auto)
  wp_join iprop(∃ (sta : AuthState) (hs' : List AuthState), tx_ptr ↦ GoInterface.ok ti ∗
      as_ptr ↦ «$r0_ptr» ∗ Lk sta Post ∗ authOwnF (.on γa) hs' ∗
      ⌜hs'.getLast? = some sta ∧ permsFit sta ∧
        ((st0.revision ≠ 0 ∧ hs' = hs) ∨ (st0.revision = 0 ∧ hs' = hs ++ [bump st0]))⌝)
    with [HL Hown tx «as»] as ⟨%sta, %hs', tx, «as», HL, Hown, %Hsta⟩
  · -- revision `0` (the buckets were empty): the first revision committed
    have h0 : st0.revision = 0 := by rw [← hxr]; rfl
    (try wp_auto)
    wp_apply (h_commit «$r0_ptr» R (.on γa) P f T ti Lk st0 Post hs st0) $$ [HL Hown]
      as ⟨%rev, %Hrev, HL, Hown⟩
    · iframe #; iframe
      ipureintro
      refine ⟨Hl0, rfl, by omega, fun _ _ => Hpk st0 Hl0 rfl (by simp), fun h => by cases h⟩
    (try wp_auto)
    (try wp_join_done)
    simp only [revAfter] at Hrev
    iexists { st0 with revision := rev }, hs ++ [bump st0]
    iframe
    ipureintro
    refine ⟨?_, hfit, Or.inr ⟨h0, rfl⟩⟩
    rw [List.getLast?_append, List.getLast?_singleton]
    simp [bump, Hrev]
  · -- else nothing
    have hn0 : st0.revision ≠ 0 := by
      intro h0
      apply Hif
      have : uint.nat xr = 0 := by rw [hxr, h0]
      word
    (try wp_auto)
    (try wp_join_done)
    iexists st0, hs
    iframe
    ipureintro
    exact ⟨hlast, hfit, Or.inl ⟨hn0, rfl⟩⟩
  -- `setupMetricsReporter()`
  wp_apply (h_metrics «$r0_ptr»)
  (try wp_auto)
  -- `refreshRangePermCache(tx)` from the transaction's state, the latest
  imod (authSnapF_of_last (.on γa) hs' sta Hsta.1) $$ Hown with ⟨Hown, #Hsnap⟩
  wp_bind (App (Val («$r0_ptr» @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
    (Val #(GoInterface.ok ti)))
  iapply (h_refresh «$r0_ptr» R (.on γa) ti (fun x => Lk x Post) sta hs') $$ [HL Hca Hown]
  · iframe Hpkg Hinv Hca Hsnap Hown
    isplitr
    · iapply HRd
    isplitl [HL]
    · iexact HL
    ipureintro; exact ⟨Hsta.2.1, fun _ _ => Hsta.1⟩
  inext
  iintro ⟨HL, Hca, Hown⟩
  ihave Hca := cacheHalf_of_at _ _ _ $$ Hca Hsnap
  (try wp_auto)
  -- `tx.Unlock()`, `be.ForceCommit()`
  wp_bind (App (Val #(methods ti.ty go!"Unlock" ti.v)) (Val #()))
  iapply HUnlock $$ %sta %Post %hs' [$HL $Hown]
  · ipureintro; exact Hsta.1
  inext
  iintro ⟨HPost, HT, Hown⟩
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
  iapply HFC $$ HT
  inext
  iintro HT
  (try wp_auto)
  iapply HΦ
  iexists «$r0_ptr», hs'
  isplitr
  · ipureintro; rfl
  iframe Hinv HPost Hown
  isplitl [Hbe2 HT Hen2 HfeA Hca]
  · iunfold authWRAt
    iframe HT Hca
    isplitl [Hbe2]
    · iframe Hbe2 Hwok
    · iunfold enabledHalf; iexists b
      isplitl [Hen2 HfeA]
      · iunfold flagAt; iframe Hen2; iunfold enG; iexact HfeA
      iunfold enabledVerdict; iexists _, st0; iframe Hst0; ipureintro; exact Hb
  isplitl [HA]
  · iunfold tpAdmin; iexists (GoInterface.ok tpi), A; iframe tokenProvider HtpA HA
  isplitr
  · ipureintro; exact Hsta.2.2
  isplitr
  · iexists _; iexact bcryptCost
  iapply (slots_rd _ «$r0_ptr» R (.on γa)) $$ [$HenS $HcaS $HbeS]

end proof

end auth
end EtcdGrove
end Perennial
