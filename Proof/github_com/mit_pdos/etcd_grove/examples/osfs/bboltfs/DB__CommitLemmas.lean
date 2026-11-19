/-
The definitions and lemmas of `DB__Commit.lean`'s proof, in a module of their own so that the
crash proofs (`DB__CommitCrash.lean`) import them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__Commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__meta
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Writer
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
-- `curMeta` stays folded (`wp_auto` unfolding it cost repeated unifications: DB__Snapshot.lean)
attribute [local irreducible] curMeta
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

theorem fileMeta_cells0 (mp : List w8) : fileMeta mp 0 = decode ((mp.drop 16).take 64) := by
  simp [fileMeta, pageMeta]

theorem fileMeta_cells1 (mp : List w8) : fileMeta mp 1 = decode ((mp.drop 4112).take 64) := by
  simp [fileMeta, pageMeta, List.drop_drop]

/-- Failing the handle under `metalock`, after a failed `commit`: `metaR` failed, `rwR`, and the
committer's token at high water mark 0. -/
theorem fail_handle (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (t n : Nat)
    (mp' : List w8) (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) :
    dbOwner (GF := GF) γ t n ∗ writerStF (GF := GF) γ db f fd p mp' fl hwm st m ∗
      (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ)) ∗ metaR (GF := GF) γ db p ⊢
      |={⊤}=> ∃ b : Bool, db.[DB, go!"failed"] ↦ b ∗
        (db.[DB, go!"failed"] ↦ true -∗ metaR (GF := GF) γ db p ∗ rwR (GF := GF) γ db f fd p ∗
          dbFailed (GF := GF) γ ∗ dbOwner (GF := GF) γ t 0) := by
  iintro ⟨Hown, Hws, Hfl, HM⟩
  iunfold dbOwner at Hown
  iunfold metaR at HM
  icases HM with ⟨%b, %mp, %mx, %hwm0, %mxc, %T, Hfa, Hcur, Hmb, %Hmx, Hauth, Hout, Hrest⟩
  unfold writerStF
  icases Hws with ⟨Hcur1, Hmap1, Hout1, Hflds1, Hw, Hcls1, Hst⟩
  icombine Hcur1 Hcur gives % ⟨_, Heq⟩
  cases Heq
  cases fl with
  | true =>
    icases Hfl with (%Hbad | ⟨-, #Hfailed⟩)
    · cases Hbad
    icases Hrest with ⟨Hfa0, %t3, Hown3⟩
    icombine Hown Hown3 gives % ⟨_, Heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
    imodintro
    iexists true
    iframe Hfa
    iintro Hfa
    isplitl [Hfa Hcur Hmb Hauth Hout Hfa0 Hown3]
    · iunfold metaR
      iexists true, mp', mx, hwm, mxc, T
      iframe Hfa Hcur Hmb Hauth Hout
      isplitr
      · ipureintro; exact Hmx
      dsimp only
      iframe Hfa0
      iexists t; iexact Hown3
    unfold dbOwner; iframe Hown
    isplitl
    · iapply rwR_of_writerSt γ db f fd p mp' true hwm st m (fun h => by cases h)
      unfold writerSt
      rcases st with _ | ⟨base, len, γm⟩ <;> dsimp only <;> iframe <;> iframe #
    · iexact Hfailed
  | false =>
    iclear Hfl
    icases Hrest with ⟨Hfail, -, -, Hown3, -⟩
    imod ghostVar_update_halves (t, 0) γ.own _ _ $$ Hown Hown3 with ⟨Hown, Hown3⟩
    imod mono_nat_own_update 1 (by omega) $$ Hfail with ⟨Hfail, #Hfailed⟩
    rcases st with _ | ⟨base, len, γm⟩
    · dsimp only
      iunfold writerExtra at Hst
      icases Hst with ⟨Hcurx, Hf2, Hfd2⟩
      imod fail_cur γ mp' hwm $$ [Hcur1 Hcurx Hcur] with ⟨Hcur1, Hcurx, Hcur⟩
      · iframe
      imodintro
      iexists false
      iframe Hfa
      iintro Hfa
      isplitl [Hfa Hcur Hmb Hauth Hout Hfail Hown3]
      · iunfold metaR
        iexists true, mp', mx, hwm, mxc, T
        iframe
        isplitr
        · ipureintro; exact Hmx
        dsimp only; iframe Hfail; iexists t; iexact Hown3
      unfold dbOwner; iframe Hown
      isplitl
      · iapply rwR_of_writerSt γ db f fd p mp' true hwm none m (fun h => by cases h)
        unfold writerSt; (try unfold writerFile)
        dsimp only
        icases Hw with ⟨%mxc', %tail, %fsz, Hfsz, Hdsz, Hf1, Hfd1, Hm, Hmx', Htail, %Hw⟩
        iframe
        isplitl
        · iunfold writerExtra; iframe; ipureintro
          exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, Hw.2.2.2.1, fun h => by cases h⟩
        · unfold dbFailed; iexact Hfailed
      · unfold dbFailed; iexact Hfailed
    · dsimp only
      icases Hst with ⟨%Hst, Htok1, #Hinv, Hwc⟩
      imod fail_cur_inv γ γ.ino base len γm mp' hwm $$ [Hinv Htok1 Hcur1 Hcur] with ⟨Htok1, Hcur1, Hcur⟩
      · iframe; iframe #
      imodintro
      iexists false
      iframe Hfa
      iintro Hfa
      isplitl [Hfa Hcur Hmb Hauth Hout Hfail Hown3]
      · iunfold metaR
        iexists true, mp', mx, hwm, mxc, T
        iframe
        isplitr
        · ipureintro; exact Hmx
        dsimp only; iframe Hfail; iexists t; iexact Hown3
      unfold dbOwner; iframe Hown
      isplitl
      · iapply rwR_of_writerSt γ db f fd p mp' true hwm (some (base, len, γm)) m (fun h => by cases h)
        unfold writerSt; (try unfold writerFile)
        dsimp only
        icases Hw with ⟨%mxc', %tail, %fsz, Hfsz, Hdsz, Hf1, Hfd1, Hm, Hmx', Htail, %Hw⟩
        iframe; iframe #; ipureintro
        first
          | exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, Hw.2.2.2.1, fun h => by cases h⟩
          | exact ⟨⟨Hw.1, Hw.2.1, Hw.2.2.1, Hw.2.2.2.1, fun h => by cases h⟩, Hst⟩
      · unfold dbFailed; iexact Hfailed

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
