/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncEpoch.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleSync`'s epoch steps on `delivInv` (SWB-5's removal mode; internal, the swift group's).
The run loop's handle on removal mode is its half of the mirror `γrm` (`swift.rmTok`,
Deliver.lean): `none` outside it, `some (M, (b, stp), d)` in it (`delivered`'s view `M`; the
record's epoch `b` and `State` pointer `stp`, the value of `γxe` deposited; `d`: the record
was reset).

* `swift.deliv_rm_start`: with every epoch pin back (the stopped epoch's `γxp` half) and the run
  loop's half of `γxe`, `delivInv` switches to removal mode (`rm = true`): the pins' half and
  `γxe`'s half are deposited and the "every executed command is in `delivered`" conjunct is
  suspended while `handleSync` removes the keys; the run loop's mirror becomes `some (M, v, false)`.
* `swift.deliv_rm_acc`: in removal mode, the view `M` is the mirror's, and can be replaced by a
  smaller one (`IterCbV`'s observations: the same `M`; `RemoveV`: `GMap.delete k M`).
* `swift.deliv_rm_exec`: the reset under `execL` (Go: `execLog = nil`), with the view empty:
  the record `γx := (b', [])`, `γxe := (b', stp')`, the pins' variable `γxp := b'`; still in
  removal mode (`acceptL`'s reset comes later), the mirror's `d := true`.
* `swift.deliv_rm_end`: the reset under `acceptL`: `γa := b'`; removal mode ends (`rm := false`);
  the run loop gets back the pins' half and `γxe`'s half at the new epoch, and its mirror `none`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- **Removal mode starts** (see the file header): the pins' half `b` and `γxe`'s half
`(b, stp)` go into `delivInv`; the run loop's mirror is now `some (M, (b, stp))`. -/
theorem swift.deliv_rm_start (E : CoPset) (hE : ↑swift.delivN ⊆ E) (γ : sp.Names) (N r : Nat)
    (γdl γx γxp γxm γa γxe γrm : GName) (str : swift.CommandId → GoString) (b : Nat) (stp : Loc) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
      ghostVar γxp (1 : Qp).half b ∗ ghostVar γxe (1 : Qp).half (b, stp) ∗
      swift.rmTok γrm none ⊢
    |={E}=> ∃ M : GMap GoString GoInterface, swift.rmTok γrm (some (M, (b, stp), false)) := by
  iintro ⟨#Hinv, Hp, Hxe, Htok⟩
  iinv Hinv with Hi Hclose
  iunfold swift.delivInv at Hi
  imod Hi
  icases Hi with ⟨%M, %bX, %X, %Mx, %rm, HM, Hx, Hpin, HMx, ⟨HX, HFz⟩, %Hok⟩
  cases rm with
  | true =>
    simp only [↓reduceIte] at *
    icases ghostVar_valid_2 γxp b (1 : Qp).half bX 1 $$ Hp Hpin with %Hv
    exfalso
    have hq := Hv.1
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    have := ((1 : Qp).half).2
    grind
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at *
    icases ghostVar_valid_2 γxp b (1 : Qp).half bX (1 : Qp).half $$ Hp Hpin with %Hv
    obtain ⟨-, rfl⟩ := Hv
    ihave Hpin1 : ghostVar γxp 1 b $$ [Hp Hpin]
    · iapply (ghostVar_split_half γxp 1 b).2
      iframe
    iunfold swift.delivX at HX
    icases HX with ⟨%bA, Ha, Hex, -, Hrm⟩
    iunfold swift.delivRm at Hrm
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold swift.rmTok at Htok
    imod ghostVar_update_halves (some (M, (b, stp), false) : swift.RmV) γrm none none $$ Htok Hrm
      with ⟨Htok, Hrm⟩
    imod Hclose $$ [HM Hx Hpin1 HMx Ha Hex Hrm Hxe HFz] with -
    · inext
      iunfold swift.delivInv
      iexists M, b, X, Mx, true
      simp only [↓reduceIte]
      iframe Hpin1 HM Hx HMx
      isplitl [Ha Hex Hrm Hxe HFz]
      · iframe HFz
        iunfold swift.delivX
        iexists bA
        iframe Ha Hex
        isplitr
        · ipureintro; intro h; cases h
        iunfold swift.delivRm
        simp only [↓reduceIte]
        iexists (b, stp), false
        iframe Hrm Hxe
        ipureintro; exact ⟨rfl, fun h => by cases h⟩
      ipureintro
      unfold swift.delivOk at Hok ⊢
      exact ⟨Hok.1, fun h => absurd h (by decide), Hok.2.2.1, Hok.2.2.2⟩
    imodintro
    iexists M
    iunfold swift.rmTok
    iexact Htok

/-- **Removal mode, an access** (see the file header): the view is the mirror's; it may be
replaced by a view with fewer keys. -/
theorem swift.deliv_rm_acc (E : CoPset) (hE : ↑swift.delivN ⊆ E) (γ : sp.Names) (N r : Nat)
    (γdl γx γxp γxm γa γxe γrm : GName) (str : swift.CommandId → GoString)
    (M : GMap GoString GoInterface) (v : Nat × Loc) (d : Bool) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
      swift.rmTok γrm (some (M, v, d)) ⊢
    |={E, E \ ↑swift.delivN}=> github_com.orcaman.concurrent_map.cmapView γdl M ∗
      (∀ M' : GMap GoString GoInterface,
        ⌜∀ k w, M'.lookup k = some w → (M.lookup k).isSome⌝ -∗
        github_com.orcaman.concurrent_map.cmapView γdl M' ={E \ ↑swift.delivN, E}=∗
        swift.rmTok γrm (some (M', v, d))) := by
  iintro ⟨#Hinv, Htok⟩
  imod (inv_acc (E := E) (N := swift.delivN) hE) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold swift.delivInv at Hi
  icases Hi with ⟨%M0, %bX, %X, %Mx, %rm, >HM, >Hx, >Hpin, >HMx, >HX, >%Hok⟩
  icases HX with ⟨HX, HFz⟩
  iunfold swift.delivX at HX
  icases HX with ⟨%bA, Ha, Hex, %HbA, Hrm⟩
  iunfold swift.rmTok at Htok
  cases rm with
  | false =>
    iunfold swift.delivRm at Hrm
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases ghostVar_valid_2 γrm _ (1 : Qp).half _ (1 : Qp).half $$ Htok Hrm with %Hv
    exact absurd Hv.2 (by simp)
  | true =>
    iunfold swift.delivRm at Hrm
    simp only [↓reduceIte]
    icases Hrm with ⟨%v0, %d0, Hrm, Hxe, %Hv0⟩
    icases ghostVar_valid_2 γrm _ (1 : Qp).half _ (1 : Qp).half $$ Htok Hrm with %Hv
    simp only [Option.some.injEq, Prod.mk.injEq] at Hv
    obtain ⟨-, rfl, rfl, rfl⟩ := Hv
    imodintro
    iframe HM
    iintro %M' %Hsub HM'
    imod ghostVar_update_halves (some (M', v, d) : swift.RmV) γrm _ _ $$ Htok Hrm with ⟨Htok, Hrm⟩
    imod Hclose $$ [HM' Hx Hpin HMx Ha Hex Hrm Hxe HFz] with -
    · inext
      iunfold swift.delivInv
      iexists M', bX, X, Mx, true
      simp only [↓reduceIte]
      iframe HM' Hx Hpin HMx
      isplitl [Ha Hex Hrm Hxe HFz]
      · iframe HFz
        iunfold swift.delivX
        iexists bA
        iframe Ha Hex
        isplitr
        · ipureintro; exact HbA
        iunfold swift.delivRm
        simp only [↓reduceIte]
        iexists v, d
        iframe Hrm Hxe
        ipureintro; exact Hv0
      ipureintro
      unfold swift.delivOk at Hok ⊢
      refine ⟨fun k w hk => ?_, fun h => absurd h (by decide), Hok.2.2.1, Hok.2.2.2⟩
      obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp (Hsub k w hk)
      exact Hok.1 k w0 hw0
    imodintro
    iunfold swift.rmTok
    iexact Htok

/-- **The reset under `execL`** (see the file header): with the view empty, the record becomes
`(b', [])` at `γxe = (b', stp')` and the pins' variable `b'`; still in removal mode. `execLInv`'s
halves of `γx`, `γxe` are the record's (`bX = b`). -/
theorem swift.deliv_rm_exec (E : CoPset) (hE : ↑swift.delivN ⊆ E) (γ : sp.Names) (N r : Nat)
    (γdl γx γxp γxm γa γxe γrm : GName) (str : swift.CommandId → GoString)
    (b bX : Nat) (stp stpX : Loc) (X : List swift.ExE) (b' : Nat) (stp' : Loc) (hb : b < b') :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
      swift.rmTok γrm (some (∅, (b, stp), false)) ∗ ghostVar γx (1 : Qp).half (bX, X) ∗
      ghostVar γxe (1 : Qp).half (bX, stpX) ⊢
    |={E}=> swift.rmTok γrm (some (∅, (b', stp'), true)) ∗
      ghostVar γx (1 : Qp).half (b', ([] : List swift.ExE)) ∗
      ghostVar γxe (1 : Qp).half (b', stp') ∗ ⌜bX = b ∧ stpX = stp⌝ := by
  iintro ⟨#Hinv, Htok, HxL, HxeL⟩
  iinv Hinv with Hi Hclose
  iunfold swift.delivInv at Hi
  imod Hi
  icases Hi with ⟨%M0, %bX0, %X0, %Mx, %rm, HM, Hx, Hpin, HMx, ⟨HX, HFz⟩, %Hok⟩
  iunfold swift.delivX at HX
  icases HX with ⟨%bA, Ha, Hex, %HbA, Hrm⟩
  iunfold swift.rmTok at Htok
  cases rm with
  | false =>
    iunfold swift.delivRm at Hrm
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases ghostVar_valid_2 γrm _ (1 : Qp).half _ (1 : Qp).half $$ Htok Hrm with %Hv
    exact absurd Hv.2 (by simp)
  | true =>
    -- round 52: removal mode (`γxp` whole) is not frozen; `delivFz`'s pieces join `delivInv`'s
    ihave ⟨-, Hpin, Hx, HMx, -⟩ := swift.delivFz_get γx γxp γxm bX0 X0 Mx true iprop(True)
      (swift.rm_noFz γxp bX0) $$ [Hpin Hx HMx HFz]
    · iframe
    iunfold swift.delivRm at Hrm
    simp only [↓reduceIte]
    icases Hrm with ⟨%v0, %d0, Hrm, Hxe, %Hv0⟩
    icases ghostVar_valid_2 γrm _ (1 : Qp).half _ (1 : Qp).half $$ Htok Hrm with %Hv
    simp only [Option.some.injEq, Prod.mk.injEq] at Hv
    obtain ⟨-, rfl, rfl, rfl⟩ := Hv
    obtain ⟨hb0, -⟩ := Hv0
    simp only at hb0
    subst hb0
    icases ghostVar_valid_2 γxe _ (1 : Qp).half _ (1 : Qp).half $$ HxeL Hxe with %Hv1
    simp only [Prod.mk.injEq] at Hv1
    obtain ⟨-, rfl, rfl⟩ := Hv1
    icases ghostVar_valid_2 γx _ (1 : Qp).half _ (1 : Qp).half $$ HxL Hx with %Hv2
    simp only [Prod.mk.injEq] at Hv2
    obtain ⟨-, -, rfl⟩ := Hv2
    imod ghostVar_update_halves (some (∅, (b', stp'), true) : swift.RmV) γrm _ _ $$ Htok Hrm
      with ⟨Htok, Hrm⟩
    imod ghostVar_update_halves (b', stp') γxe _ _ $$ HxeL Hxe with ⟨HxeL, Hxe⟩
    imod ghostVar_update_halves (b', ([] : List swift.ExE)) γx _ _ $$ HxL Hx with ⟨HxL, Hx⟩
    simp only [↓reduceIte]
    imod ghostVar_update b' γxp _ $$ Hpin with Hpin
    ihave ⟨Hx, HMx, HFz⟩ := swift.delivFz_put γx γxp γxm b' ([] : List swift.ExE) Mx $$ [Hx HMx]
    · iframe Hx HMx; iapply swift.exLb_nil
    imod Hclose $$ [HM Hx Hpin HMx Ha Hrm Hxe HFz] with -
    · inext
      iunfold swift.delivInv
      iexists ∅, b', [], Mx, true
      simp only [↓reduceIte]
      iframe HM Hx Hpin HMx
      isplitl [Ha Hrm Hxe HFz]
      · iframe HFz
        iunfold swift.delivX
        iexists bA
        iframe Ha
        isplitr
        · iapply BigSepL.bigSepL_nil.2; iempintro
        isplitr
        · ipureintro; intro h; cases h
        iunfold swift.delivRm
        simp only [↓reduceIte]
        iexists (b', stp'), true
        iframe Hrm Hxe
        ipureintro; simp
      ipureintro
      unfold swift.delivOk at Hok ⊢
      refine ⟨fun k w hk => ?_, fun h => absurd h (by decide), fun i => ?_, fun b'' i hb'' => ?_⟩
      · rw [(GMap.mapEmpty _).1 rfl k] at hk; cases hk
      · rw [Hok.2.2.2 b' i hb]; simp
      · exact Hok.2.2.2 b'' i (by omega)
    imodintro
    iunfold swift.rmTok
    iframe Htok HxL HxeL
    ipureintro; simp

/-- **Removal mode ends, under `acceptL`** (see the file header): the accepted map's epoch
becomes the record's `b'`; the run loop gets back the pins' half and `γxe`'s half at the new
epoch, and its mirror is `none`. -/
theorem swift.deliv_rm_end (E : CoPset) (hE : ↑swift.delivN ⊆ E) (γ : sp.Names) (N r : Nat)
    (γdl γx γxp γxm γa γxe γrm : GName) (str : swift.CommandId → GoString)
    (b' : Nat) (stp' : Loc) (bA : Nat) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
      swift.rmTok γrm (some (∅, (b', stp'), true)) ∗ ghostVar γa (1 : Qp).half bA ⊢
    |={E}=> swift.rmTok γrm none ∗ ghostVar γa (1 : Qp).half b' ∗
      ghostVar γxp (1 : Qp).half b' ∗ ghostVar γxe (1 : Qp).half (b', stp') := by
  iintro ⟨#Hinv, Htok, HaL⟩
  iinv Hinv with Hi Hclose
  iunfold swift.delivInv at Hi
  imod Hi
  icases Hi with ⟨%M0, %bX0, %X0, %Mx, %rm, HM, Hx, Hpin, HMx, ⟨HX, HFz⟩, %Hok⟩
  iunfold swift.delivX at HX
  icases HX with ⟨%bA0, Ha, Hex, %HbA, Hrm⟩
  iunfold swift.rmTok at Htok
  cases rm with
  | false =>
    iunfold swift.delivRm at Hrm
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases ghostVar_valid_2 γrm _ (1 : Qp).half _ (1 : Qp).half $$ Htok Hrm with %Hv
    exact absurd Hv.2 (by simp)
  | true =>
    iunfold swift.delivRm at Hrm
    simp only [↓reduceIte]
    icases Hrm with ⟨%v0, %d0, Hrm, Hxe, %Hv0⟩
    icases ghostVar_valid_2 γrm _ (1 : Qp).half _ (1 : Qp).half $$ Htok Hrm with %Hv
    simp only [Option.some.injEq, Prod.mk.injEq] at Hv
    obtain ⟨-, rfl, rfl, rfl⟩ := Hv
    obtain ⟨hb0, hX0⟩ := Hv0
    simp only at hb0
    subst hb0
    have hX0 := hX0 rfl
    subst hX0
    -- the view is empty, so is the record (`rm = false`'s conjunct holds)
    have hX : ∀ e ∈ ([] : List swift.ExE), ((∅ : GMap GoString GoInterface).lookup (str e.1)).isSome := by
      intro e he
      cases he
    imod ghostVar_update_halves (none : swift.RmV) γrm _ _ $$ Htok Hrm with ⟨Htok, Hrm⟩
    imod ghostVar_update_halves b' γa _ _ $$ HaL Ha with ⟨HaL, Ha⟩
    ihave ⟨Hpin, HpinL⟩ := (ghostVar_split_half γxp 1 b').1 $$ Hpin
    imod Hclose $$ [HM Hx Hpin HMx Ha Hex Hrm HFz] with -
    · inext
      iunfold swift.delivInv
      iexists ∅, b', [], Mx, false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe HM Hx Hpin HMx
      isplitl [Ha Hex Hrm HFz]
      · iframe HFz
        iunfold swift.delivX
        iexists b'
        iframe Ha Hex
        isplitr
        · ipureintro; intro _; rfl
        iunfold swift.delivRm
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Hrm
      ipureintro
      unfold swift.delivOk at Hok ⊢
      exact ⟨Hok.1, fun _ => hX, Hok.2.2.1, Hok.2.2.2⟩
    imodintro
    iunfold swift.rmTok
    iframe Htok HaL HpinL Hxe

end ghost

end Perennial.github_com.imdea_software.swiftpaxos
