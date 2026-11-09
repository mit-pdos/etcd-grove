/-
**Probe (B3's R1): the records' clean read over a fixed registration, lent the client's half of the
deleted entries at none** (`mvcc.NewStore.cleanRead_of_image`, `NewR.lean`). Scratch.

`keyCleanRead_of_backendC`'s proof (`BackendRecs.lean`) uses `dlInit` only in `thinV_exact_init`:
the reader's physical view is thin of the clients' logical view (`rtHeld_clean`), each missing entry
deletable (`dlIs`), which the unfixed flag refutes with no later. Over the fixed registration
(`storeDlReg`) a `dlIs` is not refutable without a later (`dlReg_dlIs` gives `▷ Φ nk`, and the goal
there is the triple's postcondition, not a WP), and nothing of the backend relates a held reader's
state to the deleted entries `dlsOwn` (whose other half is only the batch lock's, `fkHalf`). The
missing backend fact is `rtHeldDlsLaw` below; over it the lemma is proved
(`keyCleanRead_of_backendD`), with no use of the registration.

**Probe's verdict (2026-11-09, `notes/mvccfull-probe-r1.md`):** `rtHeldDlsLaw` is true of the Go code
but not provable over today's backend (nothing ties a reader's missing entries to `γ.dls`, whose two
halves are the client's and the batch lock's); a strengthening is prototyped in
`backend/RtHeldDls.lean` (`rtHeldDlsLawM_of`). Recommended instead: no backend change, the
registration fixed after `restore()`'s read (`store.Restore`'s pattern, the session over
`isKeyBackendG_of_backendC`'s registration-free contract), with `keyCleanRead_of_backendC` as is.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendRecsSnap

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode backend

section recs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The missing backend law** (R2): a held reader's state misses, of the clients' clean view and
off the hook's buckets in a safe-range bucket, only entries deleted since the open (the client's
half of the deleted entries `X`). The reader-side analogue of `backend.Snapshot`'s `dlVd` (first
clause). Not provable today: `rtHeld` keeps `thinV` (missing entries are `dlIs`, a registration
fact), nothing tying them to `γ.dls`. -/
def rtHeldDlsLaw : Prop :=
  ∀ (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (q : Qp) (vd : VData)
    (X : GMap (GoString × GoString) GoString),
    rtHeld (GF := GF) γ P b rtx rv ∗ bViewC γ q vd true ∗ dlsOwn γ X ⊢
      rtHeld γ P b rtx rv ∗ bViewC γ q vd true ∗ dlsOwn γ X ∗
      ⌜∀ nk, P.SB nk.1 = true → P.HB nk.1 = false → vd.lookup nk ≠ none →
        (vData P rv).lookup nk = none → X.lookup nk ≠ none⌝

/-- The pure step: with nothing deleted, a thin view of a `Key`-only clean view is exact. -/
theorem vData_exact_of_noDel {P : BParams} (hP : bridgeParams P) {rv : RView} {vd : VData}
    {m : Bucket} (hv : keyView vd m)
    (hsub : ∀ nk v, (vData P rv).lookup nk = some v → vd.lookup nk = some v)
    (hdl : ∀ nk, P.SB nk.1 = true → P.HB nk.1 = false → vd.lookup nk ≠ none →
      (vData P rv).lookup nk = none →
      (∅ : GMap (GoString × GoString) GoString).lookup nk ≠ none) :
    vData P rv = vd := by
  obtain ⟨-, -, hHB, hSB, -, -⟩ := hP
  apply GMap.ext
  intro nk
  cases hr : (vData P rv).lookup nk with
  | some v => exact (hsub nk v hr).symm
  | none =>
    cases hl : vd.lookup nk with
    | none => rfl
    | some w =>
      exfalso
      obtain ⟨n, k⟩ := nk
      have hn : n = go_etcd_io.etcd.server.v3.storage.schema.keyName := by
        by_cases hne : n = go_etcd_io.etcd.server.v3.storage.schema.keyName
        · exact hne
        · have := hv n k
          rw [if_neg hne] at this
          rw [this] at hl; exact absurd hl (by simp)
      exact hdl (n, k) (by rw [hSB]; simp [hn]) (by rw [hHB]; simp [hn]) (by simp [hl]) hr
        (by simp)

/-- **`ReadTx()` over a clean view, at the records, lent the deleted entries at none**
(`bridge_rt_cleanR` with `dlsOwn γ ∅` in place of `dlInit γ`, over `rtHeldDlsLaw`). -/
theorem bridge_rt_cleanD (hLaw : rtHeldDlsLaw (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b : Loc)
    (r : CmpRecs) (hpos : recsSign r) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ keySized γ P b ⊢
      □ (∀ (q : Qp) (m : Bucket),
        {{ bkViewC γ q m ∗ iprop(bkRTx γ P b ∗ dlsOwn γ ∅) }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkViewC γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnapCR (bkViewC γ) iprop(bkRTx γ P b ∗ dlsOwn γ ∅)
              (bkRecs γ r) r rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ !> %q %m %Φ !> ⟨Hv, Hrt, Hdl⟩ HΦ
  wp_apply (hRT γ P W Pk b) $$ [$Hb] as %rt #Hrtf
  iapply HΦ
  iframe Hv
  iexists iprop(bkRTx γ P b ∗ dlsOwn γ ∅)
  iframe Hrt Hdl
  iunfold keyReadSnapCR
  iintro !> %q' %Φ' !> ⟨⟨HL, Hdl⟩, Hv'⟩ HΦ'
  iunfold bkRTx at HL
  icases HL with ⟨Hrd, Ho⟩
  wp_apply (hRL γ P W Pk b rt rdOpen) $$ [$Hb $Hrtf $Hrd $Ho] as ⟨%rtx, %rv, Hh, Ho⟩
  iunfold bkViewC at Hv'
  icases Hv' with ⟨%vd, Hv', %Hvd⟩
  icases rtHeld_clean γ P b rtx rv q' vd $$ [$Hh $Hv'] with ⟨Hh, Hv', %Hcl, #Hth⟩
  icases rtHeld_fkRd γ P b rtx rv $$ Hh with ⟨Hh, #Hfk⟩
  -- nothing deleted since the open (`dlsOwn γ ∅`, lent): the thin view is exact
  icases hLaw γ P b rtx rv q' vd ∅ $$ [$Hh $Hv' $Hdl] with ⟨Hh, Hv', Hdl, %Hnd⟩
  ihave %Hsub := thinV_sub γ _ _ $$ Hth
  have Hrv : vData P rv = vd := vData_exact_of_noDel hP Hvd Hsub Hnd
  subst Hrv
  iapply HΦ'
  isplitl [Hv']
  · iunfold bkViewC
    iexists (vData P rv)
    iframe Hv'
    ipureintro; exact Hvd
  iexists (rdB rtx), iprop(rtTok γ P b rtx rv rdOpen ∗ dlsOwn γ ∅)
  isplitl [Hh Ho Hdl]
  · iframe Hdl; iunfold rtTok; iframe
  iapply keyReadLockedR_frame
  iapply rt_lockedR hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv m Hvd Hcl r hpos
    $$ [$Hpkg $Hsch $Hb $Hrtf $Hsafe $Hfk]

/-- **R1's bridge lemma over the missing law** (`mvcc.NewStore.cleanRead_of_image`'s statement with
`rtHeldDlsLaw` added; the registration premise `storeDlReg` is unused). -/
theorem keyCleanRead_of_backendD (hLaw : rtHeldDlsLaw (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (γb : GName) (γi : IdxNames)
    (r : CmpRecs) (hpos : recsSign r) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ⊢
      ∀ (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        keyCleanReadR
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) (bucketViewC γ) iprop(storeRT γ ∗ dlsOwn d.γB ∅) (kbRecs γ.kb γ.bucket r) r := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ %γ %hγ
  obtain ⟨-, hk, -⟩ := hγ
  have hv : bucketViewC (GF := GF) γ = bkViewC d.γB := by
    funext q m; unfold bucketViewC kbViewC; rw [hk]
  have hrt : storeRT (GF := GF) γ = bkRTx d.γB d.P d.be := by
    unfold storeRT kbRT bkRTx; rw [hk]
  rw [hv, hrt, hk, kbRecs_some]
  iunfold keyCleanReadR
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #d.be⟩
  isplitr
  · ipureintro; rfl
  iapply bridge_rt_cleanD hLaw hRT hrRL hrRU hrUR hID hName hSafe hP d.γB (lateW d.gx) Pk d.be r hpos
    $$ [$Hpkg $Hsch $Hb $Hsafe]

end recs

end mvcc
end EtcdGrove
end Perennial
