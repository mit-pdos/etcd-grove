/- Lean-first (no Rocq counterpart).

**`member.save`'s update of the WAL, committed on the tester's invariant** (W4c U5): the WAL state
`d` moves to `tSaveD d h es` (the save appended); the invariant's relation of the stored oracle (the
appended one, `tSaveO1`: `save` stored it before the call) to the new state is the member's candidate
`c`, at its mark (`walSyncedLb (tCandMark o c)`, which the member carries).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SavePure
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__closeLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section pure
variable [GooseExts]

/-- **A running member's WAL is accounted for by its candidate** (at the candidate's own mark). -/
theorem tMemOk_candOk0 {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d) : tCandOk o c d := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨?_, h5, h6, Nat.le_trans h7 (Nat.le_max_left _ _), h8, h9, h11⟩
  rw [h4]
  refine ⟨(tCandHist o c).length, ?_, by rw [List.length_map]; exact Nat.le_refl _, Or.inl ?_⟩
  · unfold tCandMark tCandHist; simp only [List.length_append]; omega
  · rw [← List.length_map (f := absOp), List.take_length]

theorem tSaveO1_mark (o : TOracle) (c : TCand) (h : THs) (es : List TEnt) :
    tCandMark (tSaveO1 o h es) c = tCandMark o c := rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- The appended oracle's relation to a WAL state its candidate is. -/
theorem tRelI_save1 (W : WalGS GF) (area : GoString) (o : TOracle) (c : TCand) (d : WalDur)
    (h : THs) (es : List TEnt) (hcr : o.created = true) (hc0 : c ∈ o.cands)
    (hc : tCandOk (tSaveO1 o h es) c d) (hw : tCheckWf (tSaveO1 o h es)) :
    WalFs.walSyncedLb (W := W) (tWalDir area) 0 (tCandMark o c) ∗ WalFs.walNamed (W := W) (tWalDir area) 0 ⊢
      tRelI (W := W) (GF := GF) area (tSaveO1 o h es) (some d) := by
  iintro ⟨#Hs, #Hn⟩
  unfold tRelI
  simp only [show (tSaveO1 o h es).created = true from hcr, ↓reduceIte]
  iexists d, c
  isplitr
  · ipureintro; exact ⟨rfl, hc0, hc, hw⟩
  rw [tSaveO1_mark]
  isplitl []
  · iexact Hs
  · iexact Hn

/-- **`Save`'s update, committed on the tester's invariant.** -/
theorem tInv_saveAu (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (c : TCand) (d : WalDur)
    (h : THs) (es : List TEnt) (hok : tMemOk o c d) (hes : ∀ x ∈ es, tEntWf x)
    (ht : uint.nat h.term' < 2 ^ 63)
    (hs : tSim ((tCandHist (tSaveO1 o h es) c).map absOp) (tCandMark o c)) :
    TInv (W := W) e γ ∗ tWalOwn γ (some d) ∗ tOrOwn γ (tSaveO1 o h es) none ∗
      WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark o c) ∗
      WalFs.walNamed (W := W) (tWalDir e.area) 0 ⊢
      AU <{ ∃∃ d' : WalDur, WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 d' ∗ ⌜d'.sized = true⌝ }>
          @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := W) (tWalDir e.area) 0
            { d' with H := d'.H ++ [(WalOpG.save (absHs h) (es.map absEnt)).toRaw] },
          COMM ⌜d' = d⌝ ∗ tWalOwn γ (some (tSaveD d h es)) ∗ tOrOwn γ (tSaveO1 o h es) none }> := by
  iintro ⟨#Hinv, Hwo, Hoo, #Hsl, #Hnm⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ (some d) od1 $$ Hwo Hw1
  subst hag
  ihave %hao := tOrOwn_agree (W := W) γ (tSaveO1 o h es) o1 none oa $$ Hoo Ho1
  obtain ⟨rfl, rfl⟩ := hao
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  unfold WalFs.walDiskAtI
  iexists d
  iframe Hwd
  isplitr
  · ipureintro; exact hok.2.2.2.2.2.2.2.1
  isplit
  · iintro ⟨Hwd, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, tSaveO1 o h es, none, some d; iframe; iframe #
      ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    iunfold tWalOwn at Hwo
    imod ghostVar_update_halves (some (tSaveD d h es)) γ.γw _ _ $$ Hwo Hw1 with ⟨Hwo, Hw1⟩
    have hok' := tMemOk_save1 hok h es hes ht hs
    ihave %hw1 := tRelI_checkWf e.area (tSaveO1 o h es) (some d) hok.1 $$ Hr1
    ihave #Hrel := tRelI_save1 W e.area o c (tSaveD d h es) h es hok.1 hok.2.1
      (by
        have h2 := tMemOk_candOk0 hok'
        obtain ⟨h21, h22, h23, -, h25, h26, h27⟩ := h2
        exact ⟨h21, h22, h23, Nat.le_trans hok'.2.2.2.2.2.2.1 (Nat.le_max_left _ _), h25, h26, h27⟩) hw1
      $$ [Hsl Hnm]
    · isplitl []
      · iexact Hsl
      · iexact Hnm
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, tSaveO1 o h es, none, some (tSaveD d h es)
      unfold tSaveD
      iframe; iframe #
      isplitr
      · ipureintro; exact hfile
      simp only [tRelA]
      iempintro
    imodintro
    unfold tWalOwn
    iframe
    ipureintro; rfl

end proof

end etcd_wal
end EtcdGrove
end Perennial
