/- Lean-first (no Rocq counterpart). The writer's lemmas for `Commit` and `commit`: the client
halves of mapped cells as bytes and as a typed meta; `pickMeta`'s choice is `curMeta`; the meta
cells taken out of the mapping's invariant (`out`) and put back; the meta pages' state failed;
`rwR`'s open branch as `writerSt`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commit
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapInv

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- `pickMeta`'s choice between the meta pages' metas is `curMeta`. -/
theorem pick_cur (mp : List w8) (a b : Loc) (h : metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1))
    (_ha : a ≠ null) (_hb : b ≠ null) :
    (pickMetaRes a (fileMeta mp 0) b (fileMeta mp 1) = a ∧ curMeta mp = fileMeta mp 0) ∨
    (pickMetaRes a (fileMeta mp 0) b (fileMeta mp 1) = b ∧ curMeta mp = fileMeta mp 1) := by
  unfold pickMetaRes pickValid curMeta
  dsimp only
  by_cases h1 : uint.Z (fileMeta mp 0).txid' < uint.Z (fileMeta mp 1).txid'
  · simp only [h1, ite_true]
    by_cases h2 : metaValid (fileMeta mp 1)
    · simp [h2]
    · have h0 : metaValid (fileMeta mp 0) := h.resolve_right h2
      simp [h2, h0]
  · simp only [h1, ite_false]
    by_cases h2 : metaValid (fileMeta mp 0)
    · simp [h2]
    · have h0 : metaValid (fileMeta mp 1) := h.resolve_left h2
      simp [h2, h0]

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- The client halves of mapped cells holding `B` are half of `B`'s bytes. -/
theorem cellsB_bytes (base : Loc) :
    ∀ (B : List w8) (lo : Nat), cellsB (GF := GF) base lo B ⊣⊢
      bytesPointsto (GF := GF) (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) B
  | [], lo => by
    unfold cellsB cellsR bytesPointsto
    simp only [List.length_nil, List.range'_zero]
    exact ⟨by iintro _; ipureintro; trivial, by iintro _; iapply BigSepL.bigSepL_nil.2; iempintro⟩
  | b :: B, lo => by
    refine (cellsB_cons _ _ _ _).trans ?_
    unfold bytesPointsto
    refine sep_congr .rfl ?_
    refine (cellsB_bytes base B (lo + 1)).trans ?_
    rw [loc_add_assoc, show ((lo : Nat) : Int) + 1 = ((lo + 1 : Nat) : Int) by omega]
    exact .rfl

/-- The client halves of 64 mapped cells, as half a typed meta. -/
theorem cellsB_meta (base : Loc) (lo : Nat) (B : List w8) (hB : B.length = 64)
    (hl : 0 < (base +ₗ ((lo : Nat) : Int)).addr) :
    cellsB (GF := GF) base lo B ⊣⊢
      (base +ₗ ((lo : Nat) : Int)) ↦{DFrac.own (1 : Qp).half} (decode B : Meta) := by
  refine (cellsB_bytes base B lo).trans ?_
  have := typedPointsto_bytes (GF := GF) (base +ₗ ((lo : Nat) : Int)) (decode B : Meta)
    (DFrac.own (1 : Qp).half) hl
  rw [ByteEncoding.encode_decode B hB] at this
  exact this.symm

/-- The meta cells, out of the mapping's invariant (the writer holds both mutexes, and its half
of the invariant's token, so the invariant is open), holding the metas. -/
theorem metas_out (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (hwm : Nat) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ ghostVar γ.out (1 : Qp).half.half false ⊢
      |={⊤}=> ghostVar γm (1 : Qp).half () ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
        ghostVar γ.out (1 : Qp).half.half true ∗ ghostVar γ.out (1 : Qp).half.half true ∗
        cellsB (GF := GF) base 16 ((mp.drop 16).take 64) ∗
        cellsB (GF := GF) base 4112 ((mp.drop 4112).take 64) := by
  iintro ⟨#Hinv, Htok, Hcur, Ho1, Ho2⟩
  unfold mapInv
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  rotate_left
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells at Hc
  icases Hc with ⟨%mp2, %fl2, %hwm2, Hcur2, %Hl, Hpages, Hmo⟩
  icombine Hcur Hcur2 gives % ⟨_, Heq⟩
  cases Heq
  ihave Ho := (ghostVar_split_half γ.out (1 : Qp).half false).2 $$ [Ho1 Ho2]
  · iframe
  icases Hmo with (Hout | ⟨Hout, %mc, Hc0, Hc1, %Hmc⟩)
  · icombine Ho Hout gives % ⟨_, Hbad⟩; cases Hbad
  obtain ⟨Hml, Hmc⟩ := Hmc
  have hmc := Hmc rfl
  imod ghostVar_update_halves true γ.out false false $$ Ho Hout with ⟨Ho, Hout⟩
  icases (ghostVar_split_half γ.out (1 : Qp).half true).1 $$ Ho with ⟨Ho1, Ho2⟩
  imod Hclose $$ [Hcur2 Hpages Hout] with _
  · inext; ileft
    iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells
    iexists mp, false, hwm
    isplitl [Hcur2]
    · iexact Hcur2
    isplitr
    · ipureintro; exact Hl
    iframe Hpages
    ileft; iexact Hout
  imodintro
  iframe
  have hl1 : ((mp.drop 16).take 64).length = 64 := by
    have := congrArg List.length hmc; simp at this ⊢; omega
  have h1 : mc.take 64 = (mp.drop 16).take 64 := by
    rw [hmc]; exact List.take_left' hl1
  have h2 : mc.drop 64 = (mp.drop 4112).take 64 := by
    rw [hmc]; exact List.drop_left' hl1
  rw [h1] at *; rw [h2] at *
  iframe

/-- The meta cells back into the mapping's invariant, holding the metas of `mp` unless failed. -/
theorem metas_in (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (fl : Bool) (hwm : Nat) (mc : List w8) (hmc : mc.length = 128)
    (hmp : fl = false → mc = (mp.drop 16).take 64 ++ (mp.drop 4112).take 64) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half true ∗ ghostVar γ.out (1 : Qp).half.half true ∗
      cellsB (GF := GF) base 16 (mc.take 64) ∗ cellsB (GF := GF) base 4112 (mc.drop 64) ⊢
      |={⊤}=> ghostVar γm (1 : Qp).half () ∗ ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
        ghostVar γ.out (1 : Qp).half.half false ∗ ghostVar γ.out (1 : Qp).half.half false := by
  iintro ⟨#Hinv, Htok, Hcur, Ho1, Ho2, Hc0, Hc1⟩
  unfold mapInv
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  rotate_left
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells at Hc
  icases Hc with ⟨%mp2, %fl2, %hwm2, Hcur2, %Hl, Hpages, Hmo⟩
  icombine Hcur Hcur2 gives % ⟨_, Heq⟩
  cases Heq
  ihave Ho := (ghostVar_split_half γ.out (1 : Qp).half true).2 $$ [Ho1 Ho2]
  · iframe
  icases Hmo with (Hout | ⟨Hout, %mc2, -, -, -⟩)
  rotate_left
  · icombine Ho Hout gives % ⟨_, Hbad⟩; cases Hbad
  imod ghostVar_update_halves false γ.out true true $$ Ho Hout with ⟨Ho, Hout⟩
  icases (ghostVar_split_half γ.out (1 : Qp).half false).1 $$ Ho with ⟨Ho1, Ho2⟩
  imod Hclose $$ [Hcur2 Hpages Hout Hc0 Hc1] with _
  · inext; ileft
    iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells
    iexists mp, fl, hwm
    iframe
    isplitr
    · ipureintro; exact Hl
    iright; iframe
    ipureintro; exact ⟨hmc, hmp⟩
  imodintro
  iframe

/-- The meta pages' state, failed: `cur`'s three parts, the invariant's in the invariant. -/
theorem fail_cur_inv (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (hwm : Nat) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ⊢
      |={⊤}=> ghostVar γm (1 : Qp).half () ∗ ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
        ghostVar γ.cur (1 : Qp).half (mp, true, hwm) := by
  iintro ⟨#Hinv, Htok, Hcur, Hcm⟩
  unfold mapInv
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  rotate_left
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells at Hc
  icases Hc with ⟨%mp2, %fl2, %hwm2, Hcur2, %Hl, Hpages, Hmo⟩
  icombine Hcur Hcur2 gives % ⟨_, Heq⟩
  cases Heq
  ihave Hc := (ghostVar_split_half γ.cur (1 : Qp).half (mp, false, hwm)).2 $$ [Hcur Hcur2]
  · iframe
  imod ghostVar_update_halves (mp, true, hwm) γ.cur _ _ $$ Hc Hcm with ⟨Hc, Hcm⟩
  icases (ghostVar_split_half γ.cur (1 : Qp).half (mp, true, hwm)).1 $$ Hc with ⟨Hcur, Hcur2⟩
  imod Hclose $$ [Hcur2 Hpages Hmo] with _
  · inext; ileft
    iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells
    iexists mp, true, hwm
    iframe
    isplitr
    · ipureintro; exact Hl
    icases Hmo with (Hout | ⟨Hout, %mc, Hc0, Hc1, %Hmc⟩)
    · ileft; iexact Hout
    · iright; iframe; ipureintro; exact ⟨Hmc.1, fun h => by cases h⟩
  imodintro
  iframe

/-- The meta pages' state, failed, without a mapping: `cur`'s third part is the writer's. -/
theorem fail_cur (γ : DBNames) (mp : List w8) (hwm : Nat) :
    ghostVar (GF := GF) γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ⊢
      |={⊤}=> ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
        ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
        ghostVar γ.cur (1 : Qp).half (mp, true, hwm) := by
  iintro ⟨H1, H2, Hm⟩
  ihave Hc := (ghostVar_split_half γ.cur (1 : Qp).half (mp, false, hwm)).2 $$ [H1 H2]
  · iframe
  imod ghostVar_update_halves (mp, true, hwm) γ.cur _ _ $$ Hc Hm with ⟨Hc, Hm⟩
  icases (ghostVar_split_half γ.cur (1 : Qp).half (mp, true, hwm)).1 $$ Hc with ⟨H1, H2⟩
  imodintro
  iframe

/-- `rwR`'s open branch, from the writer's part. -/
theorem rwR_of_writerSt (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (hok : fl = false → m.ok = true) :
    writerSt (GF := GF) γ db f fd p mp fl hwm st m ∗
      (match st with | none => dbFailed (GF := GF) γ | some _ => emp) ⊢
      rwR (GF := GF) γ db f fd p := by
  unfold writerSt rwR
  iintro ⟨⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, Hst⟩, Hf⟩
  ileft
  iexists mp, fl, hwm, st, m
  iframe
  isplitr
  · ipureintro; exact hok
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only; iframe
  · dsimp only; iexact Hst

end lemmas

end bboltfs
end EtcdGrove
end Perennial
