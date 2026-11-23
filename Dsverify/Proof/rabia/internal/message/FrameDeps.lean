/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/FrameDeps.lean`, run
`rabia-r1wake-1`. The lab's class `MsgPkgDeps` and `errFrameTooLongOk` (its "PENDING F", the
package state `msgState`) are the package's fact here, `message/Base.lean`'s `msgFact`.)

Internal helpers for the framing proofs (`BufWrite`, `BufRead`, ...): the frame header's pure
lemmas, `msgPkgDeps_get` (the imports' `isPkgInit`), `msgErrs_get` (the globals
`errFrameTooLarge` and `errFrameTooLong` hold non-`nil` errors), `slice_rejoin`.
-/
module

public import Dsverify.Proof.rabia.internal.message.Spec
public import Perennial.Proof.encoding.binary.Results

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model

/-! ## Pure lemmas on the frame header -/

theorem combine_foldr (d : List w8) :
    LittleEndian.combine d = d.foldr (fun b n => b.toNat + 256 * n) 0 := by
  induction d with
  | nil => rfl
  | cons b d ih => simp only [LittleEndian.combine, List.foldr_cons, ih]

theorem leToU32_toNat (d : List w8) (h : d.length = 4) :
    (leToU32 d).toNat = LittleEndian.combine d := by
  have hb := LittleEndian.combine_bound d
  rw [h] at hb
  simp only [leToU32, leToU32Def, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hb

theorem frame_eq_split (bs : List w8) : frame bs = LittleEndian.split 4 bs.length ++ bs := by
  simp only [model.frame, LittleEndian.split, Nat.div_div_eq_div_mul, List.cons_append, List.nil_append]

theorem frame_of_header (d bs : List w8) (h : d.length = 4)
    (hl : bs.length = LittleEndian.combine d) : d ++ bs = frame bs := by
  rw [frame_eq_split, hl, LittleEndian.split_combine 4 d h]

theorem u32Le_frame (bs : List w8) (n : w32) (h : n.toNat = bs.length) :
    u32Le n ++ bs = frame bs := by
  rw [frame_eq_split, ← h]; rfl

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]

/-- `isPkgInit message` holds its imports' (those the framing calls into). -/
theorem msgPkgDeps_get :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ⊢
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.binary := by
  iintro #H
  isplitr
  · solve_pkg_init
  isplitr
  · solve_pkg_init
  solve_pkg_init

/-- The package's fact (`msgFact`): the framing's two errors are non-`nil`. -/
theorem msgErrs_get :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ⊢ msgFact (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.rabia.internal.message

/-- The global `errFrameTooLarge` holds a non-nil error (the lab's `MsgPkgDeps.errInit`). -/
theorem msgPkgDeps_err :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ⊢
      ∃ e : GoInterface, globalAddr errFrameTooLarge ↦□ e ∗ ⌜e ≠ interface.nil⌝ := by
  refine msgErrs_get.trans ?_
  unfold msgFact
  iintro ⟨%e1, %e2, #H1, -, %h⟩
  iexists e1
  iframe H1
  ipureintro; exact h.1

/-- The global `errFrameTooLong` holds a non-nil error (the lab's `errFrameTooLongOk_get`). -/
theorem errFrameTooLong_get :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ⊢
      ∃ e : GoInterface, globalAddr errFrameTooLong ↦□ e ∗ ⌜e ≠ interface.nil⌝ := by
  refine msgErrs_get.trans ?_
  unfold msgFact
  iintro ⟨%e1, %e2, -, #H2, %h⟩
  iexists e2
  iframe H2
  ipureintro; exact h.2

/-- The two parts of a byte slice cut at `k`, back together. -/
theorem slice_rejoin (sl : GoSlice) (k : w64) (dq : DFrac) (vs1 vs2 : List w8)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sl.len) (h : vs1.length = sint.nat k) :
    (slice.slice sl w8 (W64 0) k ↦*{dq} vs1 ∗ slice.slice sl w8 k sl.len ↦*{dq} vs2 : IProp GF) ⊢
      sl ↦*{dq} (vs1 ++ vs2) := by
  refine Entails.trans ?_ (ownSlice_split_all k sl dq (vs1 ++ vs2) hk).2
  rw [← h, List.take_left, List.drop_left]

end defs

end Perennial.rabia.internal.message
