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

end recs

end mvcc
end EtcdGrove
end Perennial
