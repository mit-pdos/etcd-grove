/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Slot.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: accessors of the lock's contents for the executor's scan (`executeCommands`)

An instance-space slot `InstanceSpace[q][i]` (`LA_slot`), `crtInstance` (`EP_crt`, `LA_crt`), a
lower bound of `crtInstance[q]` (`LA_crtLb`), the dependencies' range (`LA_deps`).
-/
module

public import Dsverify.Proof.gryff.X.Helpers

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out committedCopy executedB inBox depR)
open Perennial.gryff.replica (XS Node nSlots rowOwn rowOwn_open rows_acc XClosed)
open Perennial.gryff.replica2 (Repl2Names rid32)
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}
variable [gryff_sem : src.gryff.Assumptions]

set_option goose.wp.extras true

/-- Slot `(q, i)` of the instance space holding `pw`: nil for no instance, else the copy. -/
def slotView (ρ : Repl2Names) (xs : XS) (s : RState) (q i : w32) (pw : Loc) : IProp GF :=
  match s.inst q i with
  | none => iprop(⌜pw = Loc.null⌝)
  | some c => iprop(⌜pw ≠ Loc.null⌝ ∗ copyRepG ρ xs (sint.Z q, sint.Z i) pw c)

theorem slotView_none {ρ : Repl2Names} {xs : XS} {s : RState} {q i : w32} {pw : Loc}
    (hc : s.inst q i = none) : slotView (GF := GF) ρ xs s q i pw = iprop(⌜pw = Loc.null⌝) := by
  unfold slotView; rw [hc]

theorem slotView_some {ρ : Repl2Names} {xs : XS} {s : RState} {q i : w32} {pw : Loc} {c : Copy}
    (hc : s.inst q i = some c) :
    slotView (GF := GF) ρ xs s q i pw =
      iprop(⌜pw ≠ Loc.null⌝ ∗ copyRepG ρ xs (sint.Z q, sint.Z i) pw c) := by
  unfold slotView; rw [hc]

theorem committedCopy_of {s : RState} {q i : w32} {c : Copy} (hb : inBox q i = true)
    (hc : s.inst q i = some c) (hs : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED) :
    committedCopy s (sint.Z q, sint.Z i) = some c := by
  have hq : BitVec.ofInt 32 (sint.Z q) = q := BitVec.ofInt_toInt
  have hi : BitVec.ofInt 32 (sint.Z i) = i := BitVec.ofInt_toInt
  simp only [inBox, decide_eq_true_eq] at hb
  unfold committedCopy
  rw [if_pos hb]
  simp only [hq, hi, hc]
  rw [if_pos hs]

theorem executedB_of {s : RState} {q i : w32} {c : Copy} (hb : inBox q i = true)
    (hc : s.inst q i = some c) (hs : c.status = model.St.EXECUTED) :
    executedB s (sint.Z q, sint.Z i) = true := by
  unfold executedB
  rw [committedCopy_of hb hc (.inr hs)]
  simp [hs]

theorem euv_set_facts {X : List Node} (euv : List w32) (qn : Nat) (e1 e' : w32)
    (he1 : euv[qn]? = some e1)
    (hf : ∀ (q : Nat) (e : w32), euv[q]? = some e →
      -1 ≤ sint.Z e ∧ ∀ i : Int, 0 ≤ i → i ≤ sint.Z e → ((q : Int), i) ∈ X)
    (hs : sint.Z e' = sint.Z e1 + 1) (hX : ((qn : Int), sint.Z e') ∈ X) :
    ∀ (q : Nat) (e : w32), (euv.set qn e')[q]? = some e →
      -1 ≤ sint.Z e ∧ ∀ i : Int, 0 ≤ i → i ≤ sint.Z e → ((q : Int), i) ∈ X := by
  intro q e h
  rw [List.getElem?_set] at h
  by_cases hq : qn = q
  · subst hq
    have hl : qn < euv.length := by
      rcases List.getElem?_eq_some_iff.1 he1 with ⟨hl, -⟩; exact hl
    simp only [hl, ite_true, Option.some.injEq] at h
    subst h
    have := hf qn e1 he1
    refine ⟨by omega, fun i hi0 hi => ?_⟩
    rcases Int.lt_or_eq_of_le hi with hlt | heq
    · exact this.2 i hi0 (by omega)
    · rw [heq]; exact hX
  · rw [if_neg hq] at h
    exact hf q e h

theorem sint32_succ (x : w32) (h : sint.Z x < 2 ^ 31 - 1) : sint.Z (x + W32 1) = sint.Z x + 1 := by
  word

theorem slotView_some_open {ρ : Repl2Names} {xs : XS} {s : RState} {q i : w32} {pw : Loc}
    {c : Copy} (hc : s.inst q i = some c) :
    slotView (GF := GF) ρ xs s q i pw ⊣⊢
      ⌜pw ≠ Loc.null⌝ ∗ copyRepG ρ xs (sint.Z q, sint.Z i) pw c := by
  rw [slotView_some hc]; exact .rfl

theorem slotView_null (ρ : Repl2Names) (xs : XS) (s : RState) (q i : w32) :
    slotView (GF := GF) ρ xs s q i Loc.null ⊢ slotView ρ xs s q i Loc.null ∗ ⌜s.inst q i = none⌝ := by
  cases hc : s.inst q i with
  | none => rw [slotView_none hc]; iintro H; iframe; ipureintro; rfl
  | some c => rw [slotView_some hc]; iintro ⟨%H, -⟩; exact absurd rfl H

theorem slotView_nn (ρ : Repl2Names) (xs : XS) (s : RState) (q i : w32) (pw : Loc)
    (hn : pw ≠ Loc.null) :
    slotView (GF := GF) ρ xs s q i pw ⊢ slotView ρ xs s q i pw ∗ ⌜(s.inst q i).isSome⌝ := by
  cases hc : s.inst q i with
  | none => rw [slotView_none hc]; iintro %H; exact absurd H hn
  | some c => rw [slotView_some hc]; iintro H; iframe; ipureintro; rfl

/-- **The slot `InstanceSpace[q][i]`** (in the box) of the EPaxos handler's heap. -/
theorem EP_slot (xs : XS) (s : RState) (q i : w32) (hb : inBox q i = true) :
    epaxosOwnG (GF := GF) ρ h r xs s ⊢ ∃ (ispS sq : GoSlice) (isp : List GoSlice)
        (ptrs : List Loc) (pw : Loc),
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      ⌜isp[(sint.Z q).toNat]? = some sq ∧ ptrs[(sint.Z i).toNat]? = some pw ∧ isp.length = 3 ∧
        ptrs.length = nSlots⌝ ∗
      sq ↦* ptrs ∗ slotView ρ xs s q i pw ∗
      (sq ↦* ptrs -∗ slotView ρ xs s q i pw -∗ epaxosOwnG ρ h r xs s) := by
  iintro HEP
  icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
    %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
  have hq3 : 0 ≤ sint.Z q ∧ sint.Z q < 3 ∧ 0 ≤ sint.Z i ∧ sint.Z i < model.SLOTS := by
    simpa [inBox] using hb
  have hqn : (sint.Z q).toNat < isp.length := by rw [Hep.1]; omega
  obtain ⟨sq, hsq⟩ : ∃ sq, isp[(sint.Z q).toNat]? = some sq := ⟨_, List.getElem?_eq_getElem hqn⟩
  icases rows_acc M isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
  icases (rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
  obtain ⟨pw, hp⟩ : ∃ pw, ptrs[(sint.Z i).toNat]? = some pw :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hrowf.1]; unfold nSlots model.SLOTS at *; omega)⟩
  have hMp := Hrowf.2 _ pw hp
  have hwn : (((sint.Z q).toNat : Nat) : Int) = sint.Z q ∧
      (((sint.Z i).toNat : Nat) : Int) = sint.Z i := by omega
  rw [hwn.1, hwn.2] at hMp
  have hqq : BitVec.ofInt 32 (sint.Z q) = q := BitVec.ofInt_toInt
  have hii : BitVec.ofInt 32 (sint.Z i) = i := BitVec.ofInt_toInt
  have hiso := Hep.2.2.2.2.2.2.1 q i hb
  iexists ispS, sq, isp, ptrs, pw
  iframe Hrow
  isplitr
  · iexact HIS
  isplitr
  · iexact Hisp
  isplitr
  · ipureintro; exact ⟨hsq, hp, Hep.1, Hrowf.1⟩
  by_cases hnull : pw = Loc.null
  · rw [if_pos hnull] at hMp
    have hc : (s.inst q i) = none := by
      rw [hMp] at hiso; simpa using hiso
    rw [slotView_none hc]
    isplitr
    · ipureintro; exact hnull
    iintro Hrow %_
    ihave Hrows := Hrows $$ [Hrow]
    · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
    iapply (epaxosOwnG_open ..).2
    iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
    iframe; iframe #; ipureintro; exact Hep
  · rw [if_neg hnull] at hMp
    icases instsG_upd ρ xs s M (sint.Z q, sint.Z i) pw hMp $$ Hinsts with
      ⟨⟨%c, %Hc, Hwi⟩, Hclose⟩
    simp only [hqq, hii] at Hc
    rw [slotView_some Hc]
    iframe Hwi
    isplitr
    · ipureintro; exact hnull
    iintro Hrow ⟨%_, Hwi⟩
    ihave Hrows := Hrows $$ [Hrow]
    · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
    ihave Hinsts := Hclose $$ %xs %s [] [] [Hwi]
    · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
    · ipureintro; intro _ _ _; rfl
    · iexists c; iframe; ipureintro; simp only [hqq, hii]; exact Hc
    iapply (epaxosOwnG_open ..).2
    iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
    iframe; iframe #; ipureintro; exact Hep

theorem ExecLaws.LA_slot (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS)
    (q i : w32) (hb : inBox q i = true) :
    L.LA t xs ⊢ ∃ (ispS sq : GoSlice) (isp : List GoSlice) (ptrs : List Loc) (pw : Loc),
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      ⌜isp[(sint.Z q).toNat]? = some sq ∧ ptrs[(sint.Z i).toNat]? = some pw ∧ isp.length = 3 ∧
        ptrs.length = nSlots⌝ ∗
      sq ↦* ptrs ∗ slotView ρ xs (stOf k t) q i pw ∗
      (sq ↦* ptrs -∗ slotView ρ xs (stOf k t) q i pw -∗ L.LA t xs) := by
  iintro HLA
  icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  icases EP_slot xs (stOf k t) q i hb $$ HEP with ⟨%ispS, %sq, %isp, %ptrs, %pw, #HIS, #Hisp,
    %Hf, Hrow, Hv, Hclose⟩
  iexists ispS, sq, isp, ptrs, pw
  iframe Hrow Hv
  isplitr
  · iexact HIS
  isplitr
  · iexact Hisp
  isplitr
  · ipureintro; exact Hf
  iintro Hrow Hv
  ihave HEP := Hclose $$ Hrow Hv
  iapply (L.LA_open ..).2; iframe

/-- `crtInstance` of the EPaxos handler's heap. -/
theorem EP_crt (xs : XS) (s : RState) :
    epaxosOwnG (GF := GF) ρ h r xs s ⊢ ∃ crtS : GoSlice,
      h.[src.gryff.EPaxosRMWHandler, go!"crtInstance"] ↦□ crtS ∗ crtS ↦* s.crtInstance ∗
      ⌜s.crtInstance.length = 3⌝ ∗ (crtS ↦* s.crtInstance -∗ epaxosOwnG ρ h r xs s) := by
  iintro HEP
  icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
    %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
  iexists crtS
  iframe Hcrtv
  isplitr
  · iexact Hcrt
  isplitr
  · ipureintro; exact Hep.2.2.1
  iintro Hcrtv
  iapply (epaxosOwnG_open ..).2
  iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
  iframe; iframe #; ipureintro; exact Hep

theorem ExecLaws.LA_crt (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) :
    L.LA t xs ⊢ ∃ crtS : GoSlice,
      h.[src.gryff.EPaxosRMWHandler, go!"crtInstance"] ↦□ crtS ∗ crtS ↦* (stOf k t).crtInstance ∗
      ⌜(stOf k t).crtInstance.length = 3⌝ ∗ (crtS ↦* (stOf k t).crtInstance -∗ L.LA t xs) := by
  iintro HLA
  icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  icases EP_crt xs (stOf k t) $$ HEP with ⟨%crtS, #Hcrt, Hcrtv, %Hl, Hclose⟩
  iexists crtS
  iframe Hcrtv
  isplitr
  · iexact Hcrt
  isplitr
  · ipureintro; exact Hl
  iintro Hcrtv
  ihave HEP := Hclose $$ Hcrtv
  iapply (L.LA_open ..).2; iframe

theorem monoNat_lb_of_bigSep (ρ : Repl2Names) (f : Fin 3 → Nat) (qf : Fin 3) :
    ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (GF := GF) (ρ.crt q) 1 (f q)) ⊢
      ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (ρ.crt q) 1 (f q)) ∗
        monoNatLbOwn (ρ.crt qf) (f qf) := by
  refine persistent_entails_left ?_
  refine ((BigSepL.bigSepL_lookup_acc (i := qf.val) (x := qf) (by simp)).1).trans ?_
  exact sep_elim_left.trans (wand_entails (monoNatLbOwn_get _ _ _))

/-- A lower bound of `crtInstance[q]`. -/
theorem ExecLaws.LA_crtLb (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS)
    (qf : Fin 3) :
    L.LA t xs ⊢ L.LA t xs ∗ monoNatLbOwn (ρ.crt qf) (sint.Z ((stOf k t).crt (rid32 qf))).toNat := by
  iintro HLA
  icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
    %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
  icases monoNat_lb_of_bigSep ρ (fun q => (sint.Z ((stOf k t).crt (rid32 q))).toNat) qf $$ Hmono
    with ⟨Hmono, #Hlb⟩
  iframe Hlb
  iapply (L.LA_open ..).2; iframe
  iapply (epaxosOwnG_open ..).2
  iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
  iframe; iframe #; ipureintro; exact Hep

/-- The dependencies' range (`th_deps`) at the lock's trace. -/
theorem ExecLaws.LA_deps (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) :
    L.Inv ∗ L.LA t xs ⊢ |={⊤}=> L.LA t xs ∗ ⌜DepsOk (stOf k t)⌝ := by
  iintro ⟨#HInv, HLA⟩
  icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  imod L.th_deps t $$ [HInv HTH] with ⟨HTH, %Hd⟩
  · iframe; iframe #
  imodintro
  isplitl
  · iapply (L.LA_open ..).2; iframe
  ipureintro; exact Hd

/-- The executed set's closure after taking the lock again. -/
theorem ExecLaws.closed_relock (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) :
    L.Inv ∗ L.TH t ∗ (⌜xs.1 = []⌝ ∨ ∃ t0, L.TLb t0 ∗
        ⌜XClosed (depR (stOf k t0)) xs.1 ∧ ∀ u ∈ xs.1, (committedCopy (stOf k t0) u).isSome⌝) ⊢
      |={⊤}=> L.TH t ∗ ⌜XClosed (depR (stOf k t)) xs.1⌝ := by
  iintro ⟨#HInv, HTH, Hcl⟩
  icases Hcl with (%Hnil | ⟨%t0, #HTLb, %Hc⟩)
  · imodintro; iframe; ipureintro
    intro x hx; rw [Hnil] at hx; cases hx
  · imod L.th_relock t0 t $$ [HTH] with ⟨HTH, %Hst⟩
    · iframe; iframe #
    imodintro; iframe; ipureintro
    exact XClosed.stable Hst.2 Hc.2 Hc.1

/-- An element of `instancesToRecover` (`recoverChanPG`): the trigger `&instanceId{q, i}` with a
lower bound of `crtInstance[q]` above `i`. -/
theorem recover_elem (ρ : Repl2Names) (pl : Loc) (q i : w32) (qf : Fin 3) (n : Nat)
    (hqf : qf.val = (sint.Z q).toNat) (hq0 : 0 ≤ sint.Z q) (hi : 0 ≤ sint.Z i)
    (hn : (sint.Z i).toNat + 1 ≤ n) :
    pl ↦ src.gryff.instanceId.mk q i ∗ monoNatLbOwn (ρ.crt qf) n ⊢ recoverChanPG (GF := GF) ρ pl := by
  unfold recoverChanPG
  iintro ⟨Hp, #Hlb⟩
  have hq3 : sint.Z q < 3 := by have := qf.isLt; omega
  iexists q, i
  iframe Hp
  isplitr
  · ipureintro; simp only [model.rowOk, decide_eq_true_eq]; omega
  iexists hq3
  have he : (⟨(sint.Z q).toNat, by omega⟩ : Fin 3) = qf := Fin.ext hqf.symm
  rw [he]
  iapply (monoNatLbOwn_le _ hn)
  iexact Hlb

/-- Reading the `Status` of the instance in a non-nil slot. -/
theorem wp_slot_Status (ρ : Repl2Names) (xs : XS) (s : RState) (q i : w32) (pw : Loc)
    (hn : pw ≠ Loc.null) :
    {{ slotView (GF := GF) ρ xs s q i pw }}
      (App (Val (GoInstruction (GoLoad go.int8))) (Val #(pw.[src.gryff.Instance, go!"Status"])))
    {{ (x : w8), RET #x; slotView ρ xs s q i pw ∗
        ⌜∃ c, s.inst q i = some c ∧ x = c.status ∧
          (c.status = model.St.EXECUTED ↔ (sint.Z q, sint.Z i) ∈ xs.1)⌝ }} := by
  iintro %Φ H HΦ
  cases hc : s.inst q i with
  | none =>
    rw [slotView_none hc]
    icases H with %H
    exact absurd H hn
  | some c =>
    rw [slotView_some hc]
    icases H with ⟨%_, Hc⟩
    icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
    iStructNamed Hp
    wp_apply IntoValTyped.wp_load (t := go.int8) _ _ _ $$ Status as Status
    ihave Hp : pw ↦ iv $$ [-HΦ Hcm Hlb]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iFrameNamed
    iapply HΦ
    isplitl
    · isplitr
      · ipureintro; exact hn
      iapply (copyRepG_open ..).2; iexists iv; iframe; ipureintro; exact Hf
    ipureintro
    exact ⟨c, rfl, Hf.2.1, Hf.2.2.2.2.2.2.2.2.2.2.2.2⟩

end

end Perennial.gryff.X
