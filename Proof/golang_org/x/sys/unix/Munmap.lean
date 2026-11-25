/-
The proof of `Spec/golang_org/x/sys/unix/Munmap.lean`: `wp_osMunmap`; when `FsNoErr` holds,
`wp_osMunmapNE` (a mapping has a cell, so the zero-length branch is not taken).
-/
module

public import Spec.golang_org.x.sys.unix.Munmap
public import Perennial.Golang.Theory.Unsafe
public import GooseLang.Ext.Fs.NoMapLockErrSpecs
public import Proof.golang_org.x.sys.unix.MunmapDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

-- `cellsR_pos`: `Proof/golang_org/x/sys/unix/MunmapDefs.lean` (a defs module, so that proofs of
-- other functions can use it, `etc/tier-check.py`).

/-- `Munmap.spec` without the error witness (session S6: a helper of the proof below). -/
private abbrev golang_org.x.sys.unix.Munmap.tripleOld : Prop :=
  ∀ (base : Loc) (len : w64) (p : Ino) (m : OsMeta) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) p (DFrac.own 1) m ∗
      cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ (e : w64), RET #(errnoErr e);
      (⌜e = 0⌝ ∗ osMeta p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps })) ∨
      (⌜e ≠ 0⌝ ∗
        (osMeta p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps }) ∨
         (osMeta p (DFrac.own 1) m ∗ cellsR base 0 len.toNat vf))) }}

/-- `Munmap.spec` over a semantics with no `munmap` error on every inode (the former `specNoErr`). -/
private abbrev golang_org.x.sys.unix.Munmap.tripleNE : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (base : Loc) (len : w64) (p : Ino) (m : OsMeta) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) p (DFrac.own 1) m ∗
      cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ RET #(errnoErr 0); osMeta p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps }) }}

private theorem golang_org.x.sys.unix.Munmap.wp_old :
    golang_org.x.sys.unix.Munmap.tripleOld (GF := GF) (hG := hG) := by
  intro base len p m vf hpos hb
  wp_start as ⟨#Hinv, Hm, Hc⟩
  by_cases hl0 : len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    iapply wp_errno
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iright; iframe
  · rw [decide_eq_false hl0]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z len := by
      simp only [sint.Z]; exact ⟨by decide, hpos⟩
    rw [if_pos h0]
    have hn : 0 < len.toNat := by
      have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    icases cellsR_pos base _ vf hn $$ Hc with ⟨Hc, %hbase⟩
    rw [show sint.Z (W64 0) = 0 from rfl, sliceIndexRef_byte ⟨base, len, len⟩ 0 hbase (Int.le_refl _)]
    have hb0 : (base +ₗ (0 : Int)) = base := by simp
    rw [hb0]
    wp_auto
    wp_apply wp_osMunmap base len len p m len.toNat vf CoPset.subseteq_top hb rfl rfl
      $$ Hinv Hm Hc as %e Hr
    iapply wp_errno
    iapply HΦ
    iexact Hr

private theorem golang_org.x.sys.unix.Munmap.wp_NE :
    golang_org.x.sys.unix.Munmap.tripleNE (GF := GF) (hG := hG) := by
  intro Sio _ hS base len p m vf hpos hb
  wp_start as ⟨#Hinv, Hm, Hc⟩
  have hl0 : len ≠ W64 0 := by rintro rfl; exact absurd hpos (by decide)
  rw [decide_eq_false hl0]
  wp_auto
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z len := by
    simp only [sint.Z]; exact ⟨by decide, hpos⟩
  rw [if_pos h0]
  have hn : 0 < len.toNat := by
    have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
  icases cellsR_pos base _ vf hn $$ Hc with ⟨Hc, %hbase⟩
  rw [show sint.Z (W64 0) = 0 from rfl, sliceIndexRef_byte ⟨base, len, len⟩ 0 hbase (Int.le_refl _)]
  have hb0 : (base +ₗ (0 : Int)) = base := by simp
  rw [hb0]
  wp_auto
  wp_apply wp_osMunmapNE hS base len len p m len.toNat vf CoPset.subseteq_top hb rfl rfl
    $$ Hinv Hm Hc as Hm
  iapply wp_errno
  iapply HΦ
  iexact Hm

/-- **`Munmap.spec`**: by cases on `FsNoErr`, the error-free triple or the one without the witness,
whose error arm then has `¬ FsNoErr`. -/
theorem golang_org.x.sys.unix.Munmap.wp_proof : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG) := by
  intro base len p m vf hpos hb
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs2
    iapply golang_org.x.sys.unix.Munmap.wp_NE Sio hSio base len p m vf hpos hb $$ Hpre
    inext
    iintro Hm
    iapply HΦ
    ileft
    iframe Hm
    ipureintro; rfl
  · iapply golang_org.x.sys.unix.Munmap.wp_old base len p m vf hpos hb $$ Hpre
    inext
    iintro %e Hr
    iapply HΦ
    icases Hr with (H | ⟨%he, H⟩)
    · ileft; iexact H
    · iright; iframe H; ipureintro; exact ⟨he, hne⟩

end proof

end EtcdGrove
end Perennial
