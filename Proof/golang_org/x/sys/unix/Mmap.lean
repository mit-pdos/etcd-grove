/-
The proof of `Spec/golang_org/x/sys/unix/Mmap.lean`: the extension's `Mmap` (`wp_osMmap`), then
`unsafe.Slice` of the base, which neither panics nor overflows since the mapping lies in the
address space.
-/
module

public import Spec.golang_org.x.sys.unix.Mmap
public import Perennial.Golang.Theory.Plain
public import GooseLang.Ext.Fs.NoMapLockErrSpecs

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

/-- `golang_org.x.sys.unix.Mmap.spec` as it was without the error witness (session S6: a helper of the proof below). -/
private abbrev golang_org.x.sys.unix.Mmap.tripleOld : Prop :=
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          osMeta d.ino (DFrac.own 1) ({ m with maps := <[base := len.toNat]> m.maps }) ∗
          ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil⌝ ∗ osMeta d.ino (DFrac.own 1) m)) }}

/-- `golang_org.x.sys.unix.Mmap.spec` over a semantics with no errors on every inode (the former `golang_org.x.sys.unix.Mmap.specNoErr`). -/
private abbrev golang_org.x.sys.unix.Mmap.tripleNE : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (base : Loc), RET (PairV #(⟨base, len, len⟩ : GoSlice) #(errnoErr 0)); osFd fd dq d ∗
      osMeta d.ino (DFrac.own 1) ({ m with maps := <[base := len.toNat]> m.maps }) ∗
      ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
        cellsR base 0 len.toNat (fun i => toCellVal bs[i]?) }}

private theorem golang_org.x.sys.unix.Mmap.wp_old : golang_org.x.sys.unix.Mmap.tripleOld (GF := GF) (hG := hG) := by
  intro fd off len prot fl dq d m hrd hoff hlen hprot hfl
  wp_start as ⟨#Hinv, Hfd, Hm⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmap fd off len prot fl dq d m CoPset.subseteq_top hrd hoff hlen hprot hfl
    $$ Hinv Hfd Hm as %base %e Hr Hfd
  icases Hr with (⟨%he, Hm, Hc⟩ | ⟨%he, Hm⟩)
  · obtain ⟨rfl, hpos, hmax⟩ := he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    wp_func_call
    wp_call
    have hnn : base ≠ null := by intro h; subst h; simp [null] at hpos
    have hlz : sint.Z len = (len.toNat : Int) := by
      simp only [sint.Z]; have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    rw [ite_eq_right (by omega), ite_eq_right hnn,
      ite_eq_right (by simp only [maxAddr] at hmax; push_cast; omega)]
    wp_auto
    rw [← show errnoErr 0 = interface.nil by unfold errnoErr; rfl]
    iapply HΦ
    iframe
    ileft
    iexists base
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨he, rfl⟩ := he
    have he' : ¬ e = W64 0 := he
    simp only [decide_eq_false he', Bool.not_false]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe
    iright
    iframe
    ipureintro; exact ⟨he, rfl⟩

private theorem golang_org.x.sys.unix.Mmap.wp_NE : golang_org.x.sys.unix.Mmap.tripleNE (GF := GF) (hG := hG) := by
  intro Sio _ hS fd off len prot fl dq d m hrd hoff hlen hprot hfl
  wp_start as ⟨#Hinv, Hfd, Hm⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmapNE hS fd off len prot fl dq d m CoPset.subseteq_top hrd hoff hlen hprot hfl
    $$ Hinv Hfd Hm as %base %he Hm Hc Hfd
  obtain ⟨hpos, hmax⟩ := he
  wp_func_call
  wp_call
  have hnn : base ≠ null := by intro h; subst h; simp [null] at hpos
  have hlz : sint.Z len = (len.toNat : Int) := by
    simp only [sint.Z]; have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
  rw [ite_eq_right (by omega), ite_eq_right hnn,
    ite_eq_right (by simp only [maxAddr] at hmax; push_cast; omega)]
  wp_auto
  rw [← show errnoErr 0 = interface.nil by unfold errnoErr; rfl]
  iapply HΦ
  iframe

/-- **`golang_org.x.sys.unix.Mmap.spec`**: by cases on `FsNoErr`, the error-free triple (`FsNoErr`'s set of inodes, its
step premises) or the triple without the witness, whose error arm then has `¬ FsNoErr`. -/
theorem golang_org.x.sys.unix.Mmap.wp_proof : golang_org.x.sys.unix.Mmap.spec (GF := GF) (hG := hG) := by
  have hM := golang_org.x.sys.unix.Mmap.wp_old (GF := GF) (hG := hG)
  have hNE := golang_org.x.sys.unix.Mmap.wp_NE (GF := GF) (hG := hG)
  intro fd off len prot fl dq d m hrd hoff hlen hprot hfl
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs2
    iapply hNE Sio hSio fd off len prot fl dq d m hrd hoff hlen hprot hfl $$ Hpre
    inext
    iintro %base ⟨Hfd, Hm, Hc⟩
    iapply HΦ
    iframe Hfd
    ileft
    iexists base
    iframe Hm Hc
    ipureintro; exact ⟨rfl, rfl⟩
  · iapply hM fd off len prot fl dq d m hrd hoff hlen hprot hfl $$ Hpre
    inext
    iintro %sl %e ⟨Hfd, Hr⟩
    iapply HΦ
    iframe Hfd
    icases Hr with (H | ⟨%he, Hm⟩)
    · ileft; iexact H
    · iright; iframe Hm; ipureintro; exact ⟨he.1, he.2, hne⟩

end proof

end EtcdGrove
end Perennial
