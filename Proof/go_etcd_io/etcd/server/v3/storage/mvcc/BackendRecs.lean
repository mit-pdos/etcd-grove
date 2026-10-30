/-
**The compaction records, read from the real backend** (the M2 storage plan's items 27/29/30,
branch `m2-backend`, 2026-10-30): the held shared read transaction's reads of `Meta`'s two
compaction keys, while the client's half of the backend's compaction-key flag stands where it was at
the open (`backend.fkOpen`, `backend.fkRd_open`), find the open's values; when those are the bytes of
the records `r` (`CmpRecs`), the read is `metaReadSpecR … (some r)`, the records exactly
(`rt_metaRecs`). The records' part of the restore chain's clean read (`keyCleanRead_of_backendC`);
no `dlNoDel`, no new trust.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreRecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode backend

section recs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The compaction-key values of the records `r`**: each key's value the bytes of its record
(`RevToBytes(Revision{Main: x})`), absent if the record is. -/
def recsVals (r : CmpRecs) : FkVals :=
  (r.fin.map (fun x => revBytes ⟨x, W64 0⟩ false), r.sched.map (fun x => revBytes ⟨x, W64 0⟩ false))

/-- The value `recsVals r` gives a compaction key is its record's bytes. -/
theorem fkAt_recsVals (r : CmpRecs) {kn : GoString} (h : metaCompactKey kn) :
    fkAt (recsVals r) kn = (r.at kn).map (fun x => revBytes ⟨x, W64 0⟩ false) := by
  unfold fkAt recsVals CmpRecs.at
  rcases h with rfl | rfl
  · have h1 : schedKeyBytes ≠ go!"finishedCompactRev" := by decide
    have h2 : schedKeyBytes ≠ finKeyBytes := by decide
    rw [if_neg h1, if_neg h2]
  · simp [finKeyBytes]

/-- **The held shared read transaction's reads of the `Meta` bucket's compaction keys at the
records** (items 27/29/30): with the client's half of the backend's compaction-key flag at its
value `n` at the open, over data whose compaction keys held the records' bytes (`fkOpen γ n
(recsVals r)`), and the reader's witness (`fkRd`), the read of a compaction key finds its record:
nothing if absent, else the key and the record's bytes (`metaReadSpecR … (some r)`), its records
being revisions (`hpos`). -/
theorem rt_metaRecs (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (qo : Qp) (r : CmpRecs) (n : Nat)
    (hpos : ∀ kn x, metaCompactKey kn → r.at kn = some x → 0 ≤ sint.Z x) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ fkRd γ P rv ∗ fkOwn γ n ∗
      fkOpen γ n (recsVals r) ⊢
      fkOwn γ n ∗
        metaReadSpecR ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
          (some r) (rdB rtx) (rtTok γ P b rtx rv qo) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt, #Hfk, Ho, #Hop⟩
  icases fkRd_open γ P rv n (recsVals r) $$ [$Ho $Hop $Hfk] with ⟨Ho, %Hval⟩
  iframe Ho
  by_cases hne : r = CmpRecs.empty
  · -- no record: the open's values are none, the reads find nothing
    subst hne
    rw [metaReadSpecR_empty]
    iunfold metaReadSpec
    iintro %bk %key %kn %dq %Hkn !> %Φ ⟨#HM, Ht, Hkey⟩ HΦ
    iunfold rtTok at Ht
    icases Ht with ⟨Hh, Ho⟩
    ihave #Hbk := meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
    ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    iapply wp_fupd
    wp_apply (rtUR_held hUR γ P W Pk b rt rtx rv qo bk metaBI key slice.nil kn [] dq DFrac.discard
        (W64 0) (by simp) (Or.inl (by simp [rangeLimit])) hP.2.1) $$ [$Hb $Hrt $Hh $Ho $Hbk $Hkey $Hnil]
        as %ks %vs ⟨Hh, Ho, Hkey, -, Hout⟩
    icases rtHeld_wf γ P b rtx rv $$ Hh with ⟨Hh, %HrW⟩
    irevert Hout
    rw [rtRange_single P rv metaBI kn (W64 0) hP.2.1 HrW,
      vOf_fkVal Hval hP.2.1 (fkKey_meta Hkn), fkAt_recsVals _ Hkn]
    simp only [CmpRecs.at, CmpRecs.empty, ite_self, Option.map_none]
    iintro Hout
    imod kvsOutRd_nil _ rtx ks vs $$ Hout with ⟨#Hk, #Hv⟩
    imodintro
    iapply HΦ
    iframe Hkey
    isplitl [Hh Ho]
    · iunfold rtTok; iframe
    ileft
    iframe Hk Hv
  · unfold metaReadSpecR
    simp only [hne, ↓reduceIte]
    iintro %bk %key %kn %dq %Hkn !> %Φ ⟨#HM, Ht, Hkey⟩ HΦ
    iunfold rtTok at Ht
    icases Ht with ⟨Hh, Ho⟩
    ihave #Hbk := meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
    ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    iapply wp_fupd
    wp_apply (rtUR_held hUR γ P W Pk b rt rtx rv qo bk metaBI key slice.nil kn [] dq DFrac.discard
        (W64 0) (by simp) (Or.inl (by simp [rangeLimit])) hP.2.1) $$ [$Hb $Hrt $Hh $Ho $Hbk $Hkey $Hnil]
        as %ks %vs ⟨Hh, Ho, Hkey, -, Hout⟩
    icases rtHeld_wf γ P b rtx rv $$ Hh with ⟨Hh, %HrW⟩
    irevert Hout
    rw [rtRange_single P rv metaBI kn (W64 0) hP.2.1 HrW,
      vOf_fkVal Hval hP.2.1 (fkKey_meta Hkn), fkAt_recsVals _ Hkn]
    cases hx : r.at kn with
    | none =>
      simp only [Option.map_none]
      iintro Hout
      imod kvsOutRd_nil _ rtx ks vs $$ Hout with ⟨#Hk, #Hv⟩
      imodintro
      iapply HΦ
      iframe Hkey
      isplitl [Hh Ho]
      · iunfold rtTok; iframe
      ileft
      iframe Hk Hv
    | some x =>
      simp only [Option.map_some]
      iintro Hout
      imod kvsOutRd_single _ rtx ks vs kn _ $$ Hout with ⟨%ksl, %vsl, #Hk, #Hrk1, #Hv, #Hrv1⟩
      imodintro
      iapply HΦ
      iframe Hkey
      isplitl [Hh Ho]
      · iunfold rtTok; iframe
      iright
      iexists ksl, vsl, x
      iframe Hk Hv Hrk1 Hrv1
      ipureintro; exact ⟨rfl, hpos kn x Hkn hx⟩

/-- **The records' resource of the real backend** (item 27's `kbRecs` at a real instance): at no
record, today's no-compaction token; else the client's half of the compaction-key flag at its
value at the open, over data whose compaction keys held the records' bytes. -/
def bkRecs (γ : BNames) (r : CmpRecs) : IProp GF :=
  if r = CmpRecs.empty then bkNoCmp γ else iprop(∃ n : Nat, fkOwn γ n ∗ fkOpen γ n (recsVals r))

/-- **The held read transaction at the records** (`rt_locked` with the records' meta clause,
`rt_metaRecs`). -/
theorem rt_lockedR (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    {P : BParams} (hP : bridgeParams P) (γ : BNames) (W Pk : IProp GF) (b rt rtx : Loc)
    (rv : RView) (m : Bucket) (hv : keyView (vData P rv) m) (hcl : rbClean P rv.2)
    (r : CmpRecs) (hpos : recsSign r) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ keySized γ P b ∗ fkRd γ P rv ⊢
      keyReadLockedR (bkRTx γ P b) (bkRecs γ r) r true
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩
        m (rdB rtx) (rtTok γ P b rtx rv rdOpen) true := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt, #Hsafe, #Hfk⟩
  ihave #Hl := rt_locked hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv m hv true (fun _ => hcl)
    $$ [$Hpkg $Hsch $Hb $Hrt $Hsafe $Hfk]
  by_cases he : r = CmpRecs.empty
  · subst he
    have hnc : bkRecs (GF := GF) γ CmpRecs.empty = bkNoCmp γ := by unfold bkRecs; simp
    rw [hnc, keyReadLockedR_empty]
    iexact Hl
  · iapply keyReadLockedR_of_locked (NC' := bkNoCmp γ)
    iframe Hl
    iintro !> Hnc
    have hnc : bkRecs (GF := GF) γ r = iprop(∃ n : Nat, fkOwn γ n ∗ fkOpen γ n (recsVals r)) := by
      unfold bkRecs; simp [he]
    rw [hnc]
    icases Hnc with ⟨%n, Ho, #Hop⟩
    icases rt_metaRecs hUR hID hName hSafe hP γ W Pk b rt rtx rv rdOpen r n
      (fun kn x _ hx => recsSign_at r hpos kn x hx) $$ [$Hpkg $Hsch $Hb $Hrt $Hfk $Ho $Hop]
      with ⟨Ho, #Hm⟩
    isplitl [Ho]
    · iexists n; iframe Ho Hop
    iintro !>
    iexact Hm

/-- **`ReadTx()` over a clean view, at the records, with the registration not yet fixed** (item 30,
2026-10-30; `bridge_rt_clean` over `dlInit`, lent with the reader's token, in place of `dlNoDel`):
the read transaction's snapshot is the bucket itself, its reads of the compaction keys the records
`r` (under `bkRecs γ r`), the records being revisions. -/
theorem bridge_rt_cleanR (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
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
        {{ bkViewC γ q m ∗ iprop(bkRTx γ P b ∗ dlInit γ) }}
          (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            go!"ReadTx" #b)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); bkViewC γ q m ∗
            ∃ L : IProp GF, L ∗ keyReadSnapCR (bkViewC γ) iprop(bkRTx γ P b ∗ dlInit γ)
              (bkRecs γ r) r rt m L }}) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ !> %q %m %Φ !> ⟨Hv, Hrt, Hdl⟩ HΦ
  wp_apply (hRT γ P W Pk b) $$ [$Hb] as %rt #Hrtf
  iapply HΦ
  iframe Hv
  iexists iprop(bkRTx γ P b ∗ dlInit γ)
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
  -- nothing made deletable yet (`dlInit`, lent): the thin view is exact
  icases backend.thinV_exact_init γ (vData P rv) vd $$ [$Hdl $Hth] with ⟨Hdl, %Hrv⟩
  subst Hrv
  iapply HΦ'
  isplitl [Hv']
  · iunfold bkViewC
    iexists (vData P rv)
    iframe Hv'
    ipureintro; exact Hvd
  iexists (rdB rtx), iprop(rtTok γ P b rtx rv rdOpen ∗ dlInit γ)
  isplitl [Hh Ho Hdl]
  · iframe Hdl; iunfold rtTok; iframe
  iapply keyReadLockedR_frame
  iapply rt_lockedR hRU hUR hID hName hSafe hP γ W Pk b rt rtx rv m Hvd Hcl r hpos
    $$ [$Hpkg $Hsch $Hb $Hrtf $Hsafe $Hfk]

/-- **The records' clean read of a compacting real backend** (item 30, proved 2026-10-30, in the
form the plan's D1/D2 repairs give it): `keyCleanRead_of_backend`'s, with the new backend's
registration not yet fixed (`dlInit`, lent with the reader's token: `kv.Restore` reads before it
fixes the store's deletable keys) in place of `dlNoDel`, at the records `r` the client's
compaction-key flag stands at since the open (`bkRecs`), the records being revisions
(`recsSign`, from `recsOk`). -/
theorem keyCleanRead_of_backendC
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (γb : GName) (r : CmpRecs)
    (hpos : recsSign r) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ⊢
      ∀ (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d⌝ →
        keyCleanReadR
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) (bucketViewC γ) iprop(storeRT γ ∗ dlInit d.γB) (bkRecs d.γB r) r := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsafe⟩ %γ %hγ
  obtain ⟨-, hk⟩ := hγ
  have hv : bucketViewC (GF := GF) γ = bkViewC d.γB := by
    funext q m; unfold bucketViewC kbViewC; rw [hk]
  have hrt : storeRT (GF := GF) γ = bkRTx d.γB d.P d.be := by
    unfold storeRT kbRT bkRTx; rw [hk]
  rw [hv, hrt]
  iunfold keyCleanReadR
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #d.be⟩
  isplitr
  · ipureintro; rfl
  iapply bridge_rt_cleanR hRT hrRL hrRU hrUR hID hName hSafe hP d.γB (lateW d.gx) Pk d.be r hpos
    $$ [$Hpkg $Hsch $Hb $Hsafe]

end recs

end mvcc
end EtcdGrove
end Perennial
