/-
**B3 (mvccfull F1): `NewStore` over an image, its pieces** (`NewStore.lean`'s proof): the caller's
fresh index names grown to the image's log (`idxFresh_image`), the image normalized across the
modes (`restoreImageM_norm`: off, the whole bucket at no record is a cut image), its view a thin
view of the log (`bucketViewL_image`) and the tracked compaction at the image (`cmpTrack_image`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCmp
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Fresh index names at a log `L`** (`NewStore` over an image; `idxFresh_split` at `L = []`): the
history and the committed log's authorities grown to `L`, the event count's authority at `L`'s
events (what the rebuild puts, `newTreeIndex`'s `n`), the compaction revision's at `c`; the writer's
handle at `L` without its receipts (`idxWriterNR`, whose receipt the rebuild gives), the other half of
the committed log's authority, and the lower bounds `restore` and the index's lock take. -/
theorem idxFresh_image (γ : IdxNames) (L : Log) (c : Int) (hwf : IdxWf L []) (hc : -1 ≤ c) :
    idxFresh (GF := GF) γ ⊢ |==> (monoNatAuthOwn γ.nev 1 (evsOf (L ++ [[]])).length ∗
      ghostVar γ.cmp 1 ((-1 : Int), ([] : List Loc)) ∗ crevLb γ (-1) ∗
      monoListLbOwn γ.log L ∗ idxWriterNR γ L [] ∗ idxLogAuth γ (1 : Qp).half L ∗
      crevUB γ 1 c ∗ crevLb γ c ∗ idxWriterLb γ L) := by
  iintro Hfresh
  iunfold idxFresh at Hfresh
  icases Hfresh with ⟨Hhauth, -, Hnauth, -, Hlauth, -, Hcauth, #Hclb, Hcmp⟩
  imod monoListAuthOwn_update_app (histShape L []) $$ Hhauth with ⟨Hhauth, #Hhlb⟩
  imod monoListAuthOwn_update_app L $$ Hlauth with ⟨Hlauth, #Hllb⟩
  imod mono_nat_own_update (evsOf (L ++ [[]])).length (Nat.zero_le _) $$ Hnauth with ⟨Hnauth, #Hnlb⟩
  imod mono_nat_own_update (crevN c) (Nat.zero_le _) $$ Hcauth with ⟨Hcauth, #Hcclb⟩
  simp only [List.nil_append]
  have hhalves := (monoListAuthOwn_fractional (GF := GF) γ.log L).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hhalves
  icases hhalves.1 $$ Hlauth with ⟨Hlauth, Hlother⟩
  imodintro
  iframe Hnauth Hcmp Hllb Hlother
  isplitl []
  · iunfold crevLb; rw [crevN_neg]; iexact Hclb
  isplitl [Hhauth Hlauth]
  · iunfold idxWriterNR
    iframe Hhauth Hlauth Hnlb
    ipureintro; exact hwf
  isplitl [Hcauth]
  · iunfold crevUB; iexact Hcauth
  isplitl []
  · iunfold crevLb; iexact Hcclb
  iunfold idxWriterLb
  iframe Hhlb Hnlb
  ipureintro; exact hwf

/-- **The image, in either mode** (`restoreImageM`): a clean view of entries `ents` cut at the
records' revision, the records' resource (`kbRecs`) and the values' halves at the records; off, at
no record and the whole log's entries (the bucket of the log). -/
theorem restoreImageM_norm (d : KBReal) (γb : GName) (L : Log) (r : CmpRecs) :
    restoreImageM (GF := GF) d γb L r ⊢ ∃ ents : List KvEnt,
      kbViewC (some d) γb 1 (bucketOfEnts ents) ∗ kbRecs (some d) γb r ∗
      kbVals (some d) (recBytes r.fin, recBytes r.sched) ∅ ∗
      ⌜recsOk L r ∧ recsPos r ∧ entsCutAt L r.crev ents ∧
        (d.cm = false → r = CmpRecs.empty ∧ ents = logEnts L 0 L.length)⌝ := by
  cases hcm : d.cm with
  | true =>
    unfold restoreImageM
    simp only [hcm, ↓reduceIte]
    iintro ⟨%ents, Hv, ⟨Hr, Hvals⟩, -, %Hok⟩
    iexists ents
    iframe Hv Hr Hvals
    ipureintro
    exact ⟨Hok.1, Hok.2.1, Hok.2.2, fun h => absurd h Bool.true_ne_false⟩
  | false =>
    iintro H
    icases (restoreImageM_off d γb L r hcm).1 $$ H with ⟨Hv, Hnc, %hr⟩
    subst hr
    icases (kbNoCmp_split (some d) γb).1 $$ Hnc with ⟨Hf, Hvals⟩
    iexists logEnts L 0 L.length
    rw [bucketOfEnts_logEnts, kbRecs_empty]
    iframe Hv Hf
    isplitl [Hvals]
    · simp only [CmpRecs.empty, recBytes, Option.map_none]
      iexact Hvals
    ipureintro
    refine ⟨⟨fun x h => by simp [CmpRecs.empty] at h, fun x h => by simp [CmpRecs.empty] at h⟩,
      ⟨fun x h => by simp [CmpRecs.empty] at h, fun x h => by simp [CmpRecs.empty] at h⟩,
      entsCutAt_full L _, fun _ => ⟨rfl, rfl⟩⟩

/-- **The image's view is a thin view of the log**: on, its keys missing are deletable at the
records' revision (`bucketViewL_ofCut`); off, it is the log's bucket (`bucketViewL_exact`). -/
theorem bucketViewL_image (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d) (q : Qp) (L : Log)
    (hb : LogB L) (r : CmpRecs) (ents : List KvEnt) (hcut : entsCutAt L r.crev ents)
    (hoff : d.cm = false → r = CmpRecs.empty ∧ ents = logEnts L 0 L.length) (hc : -1 ≤ r.crev) :
    bucketView (GF := GF) γ q (bucketOfEnts ents) ∗ crevLb γ.idx r.crev ∗ idxCert γ.idx L ⊢
      bucketViewL γ q L := by
  cases hcm : d.cm with
  | true =>
    iintro ⟨Hv, #Hlb, #Hc⟩
    iapply bucketViewL_ofCut γ q L hb r.crev ents hcut hc
    iframe Hv Hlb Hc
    ipureintro; simp [kbCmpM, hk, hcm]
  | false =>
    obtain ⟨-, he⟩ := hoff hcm
    subst he
    rw [bucketOfEnts_logEnts]
    iintro ⟨Hv, -, -⟩
    iapply bucketViewL_exact $$ Hv

/-- **The tracked compaction at the image** (`cmpTrack_restored` on; off, nothing, the values given
back for the writer's loan). -/
theorem cmpTrack_image (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d) (L : Log) (hb : LogB L)
    (r : CmpRecs) (ents : List KvEnt) (hrec : recsOk L r) (hpos : recsPos r)
    (hcut : entsCutAt L r.crev ents) :
    kbVals (GF := GF) (some d) (recBytes r.fin, recBytes r.sched) ∅ ∗
      ghostVar γ.rcv (1 : Qp).half r.crev ∗
      ghostVar γ.jc (1 : Qp).half (r.finRev, (⟨W64 0, W64 0⟩ : Rev)) ∗
      monoNatAuthOwn γ.rcl 1 (crevN r.crev) ⊢
      cmpTrack γ L (bucketOfEnts ents) r ∗
        (⌜d.cm = false⌝ -∗ kbVals (some d) (recBytes r.fin, recBytes r.sched) ∅) := by
  cases hcm : d.cm with
  | true =>
    iintro H
    isplitl [H]
    · iapply cmpTrack_restored γ d hk hcm L hb r ents hrec hpos hcut $$ H
    · iintro %h; exact absurd h Bool.true_ne_false
  | false =>
    iintro ⟨Hv, -, -, -⟩
    isplitr
    · unfold cmpTrack; rw [hk]; simp only [hcm, Bool.false_eq_true, ↓reduceIte]; itrivial
    · iintro -; iexact Hv

end lemmas

end mvcc
end EtcdGrove
end Perennial
