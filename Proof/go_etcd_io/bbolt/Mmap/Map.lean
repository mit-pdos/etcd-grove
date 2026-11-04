/-
bbolt's `mmap(db, sz)` (`bolt_unix.go`; U4, `notes/bbolt-proof-plan.md`): `unix.Mmap` of the
file, `unix.Madvise(MADV_RANDOM)`, then `dataref`, `data` and `datasz` set. Three outcomes:
mapped (the fields set, the new mapping's cells holding the file's page cache); `Mmap` failed
(nothing changed, an errno); `Madvise` failed (the mapping made but the fields unchanged, an
`fmt.Errorf` error: the mapping leaks, design B6.1's junk).

`db.MmapFlags` must be `0` or `MAP_POPULATE` (`unix.Mmap`'s spec admits only these): `dbFixed`
leaves it any `int` (U4 finding).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.ErrPtr
public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.golang_org.x.sys.unix.Mmap
public import Spec.golang_org.x.sys.unix.Madvise
public import Spec.os.File__Fd
public import Spec.fmt.Errorf
public import Proof.golang_org.x.sys.unix.Munmap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section map
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.data`'s type, `*[MaxMapSize]byte`, points to a plain array (the conversion from
`unsafe.Pointer` has a rule). -/
instance maxMapArray_isPlain :
    go.IsPlain (go.GoType.ArrayType 281474976710655 go.byte) (281474976710655 * 1) :=
  ⟨1, .array 281474976710655 go.byte 1 1 (.scalar _ _ .isPlainScalar_uint8) (by decide)⟩

/-- The new mapping's cells: the file's page cache `bs` (`unix.Mmap`'s). -/
def mapCells (base : Loc) (sz : w64) (m : OsMeta) : IProp GF :=
  iprop(∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
    cellsR base 0 sz.toNat (fun i => toCellVal bs[i]?))

/-- **`mmap(db, sz)`** (over the fields it writes, the file and its `OsMeta`). -/
abbrev mmapF.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqf dqo dqd : DFrac) (mf : w64) (m : OsMeta)
    (sz : w64) (x : GoSlice) (y : Loc) (z : w64),
  (mf = W64 0 ∨ mf = W64 0x8000) → 0 < sz.toInt →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p dqo ∗ osFd fd dqd ⟨p, true, true⟩ ∗
      db.[DB, go!"MmapFlags"] ↦□ mf ∗ osMeta p (DFrac.own 1) (some m) ∗
      db.[DB, go!"dataref"] ↦ x ∗ db.[DB, go!"data"] ↦ y ∗ db.[DB, go!"datasz"] ↦ z }}
    (App (App (Val #(functions mmap [])) (Val #db)) (Val #sz))
  {{ (err : GoInterface), RET #err;
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p dqo ∗ osFd fd dqd ⟨p, true, true⟩ ∗
      ((∃ base : Loc, ⌜err = interface.nil ∧ 0 < base.addr⌝ ∗
          db.[DB, go!"dataref"] ↦ (⟨base, sz, sz⟩ : GoSlice) ∗ db.[DB, go!"data"] ↦ base ∗
          db.[DB, go!"datasz"] ↦ sz ∗
          osMeta p (DFrac.own 1) (some { m with maps := <[base := sz.toNat]> m.maps }) ∗
          mapCells base sz m) ∨
       (db.[DB, go!"dataref"] ↦ x ∗ db.[DB, go!"data"] ↦ y ∗ db.[DB, go!"datasz"] ↦ z ∗
         ⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err ∗
         (osMeta p (DFrac.own 1) (some m) ∨
          (∃ base : Loc, ⌜0 < base.addr⌝ ∗
            osMeta p (DFrac.own 1) (some { m with maps := <[base := sz.toNat]> m.maps }) ∗
            mapCells base sz m)))) }}

theorem mmapF.wp_proof (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hMmap : golang_org.x.sys.unix.Mmap.spec (GF := GF) (hG := hG))
    (hMadvise : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    mmapF.spec (GF := GF) (hG := hG) := by
  intro db f fd p dqf dqo dqd mf m sz x y z hmf hsz
  wp_start as ⟨#Hos, Hf, Hfo, Hfd, #Hmf, Hm, Hdr, Hd, Hsz⟩
  wp_auto
  wp_apply hFd f fd p dqo $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  have hfl : (W64 1 ||| mf).toNat = MAP_SHARED ∨ (W64 1 ||| mf).toNat = MAP_SHARED + MAP_POPULATE := by
    rcases hmf with rfl | rfl
    · left; rfl
    · right; rfl
  wp_apply hMmap fd (W64 0) sz (W64 1) (W64 1 ||| mf) dqd ⟨p, true, true⟩ m rfl rfl hsz rfl hfl
    $$ [Hfd Hm] as %sl %e ⟨Hfd, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%base, %Hbe, Hm, %bs, %Hbs, Hc⟩ | ⟨%Hbe, Hm⟩)
  · obtain ⟨rfl, rfl⟩ := Hbe
    simp only [errnoErr, ↓reduceIte]
    wp_auto
    wp_apply hMadvise _ (W64 1) (by decide) as %e2 -
    try wp_auto
    have hszn : 0 < sz.toNat := by have := hsz; simp [BitVec.toInt] at this; omega
    icases cellsR_pos _ _ _ hszn $$ Hc with ⟨Hc, %Hpos⟩
    ihave Hfo : fileOwn f fd p dqo $$ [Hfo]
    · rw [fileOwn_eq]; iexact Hfo
    by_cases h0 : e2 = 0
    · subst h0
      simp only [errnoErr, ↓reduceIte]
      wp_auto
      have hz : sint.Z (W64 0) = 0 := rfl
      have hs : 0 < sint.Z sz := hsz
      rw [hz, ite_eq_left_of_eq_true _ _ (eq_true (⟨Int.le_refl _, hs⟩ : _ ∧ _)),
        sliceIndexRef_byte _ _ Hpos (Int.le_refl _)]
      simp only [loc_add_0]
      wp_auto
      iapply HΦ
      iframe Hf Hfo Hfd
      ileft
      iexists base
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Hpos⟩
      · unfold mapCells; iexists bs; iframe; ipureintro; exact Hbs
    · simp only [errnoErr, h0, ↓reduceIte]
      wp_auto
      by_cases h38 : e2 = W64 38
      · subst h38
        wp_auto
        have hz : sint.Z (W64 0) = 0 := rfl
        have hs : 0 < sint.Z sz := hsz
        rw [hz, ite_eq_left_of_eq_true _ _ (eq_true (⟨Int.le_refl _, hs⟩ : _ ∧ _)),
          sliceIndexRef_byte _ _ Hpos (Int.le_refl _)]
        simp only [loc_add_0]
        wp_auto
        iapply HΦ
        iframe Hf Hfo Hfd
        ileft
        iexists base
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, Hpos⟩
        · unfold mapCells; iexists bs; iframe; ipureintro; exact Hbs
      · rw [decide_eq_false h38]
        wp_auto
        have hS := hErr e2 h0
        simp only [errnoErr, h0, ↓reduceIte, interface.mkOk, fmtErrorOk] at hS
        have hS' := hS.trans (sep_elim_right (P := iprop(⌜_⌝)))
        ihave #HeS := hS'
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_apply hErrorf _ _ _ _ $$ [$Hsl] as %ii ⟨-, #HiS⟩
        · iframe
          simp only [fmt.argsOk, fmt.argOk]
          isplitl
          · iright; ileft; iapply HeS; iempintro
          · itrivial
        try wp_auto
        iapply HΦ
        iframe Hf Hfo Hfd
        iright
        iframe Hdr Hd Hsz
        icases HiS with ⟨#HiS, %Hty, %Hptr⟩
        isplitr
        · ipureintro; exact ⟨(fun h => nomatch h), errPtrTyped_of_ptr _ Hptr⟩
        isplitr
        · simp only [fmtErrorOk, noArgStringSig]
          iframe HiS; ipureintro; exact Hty
        · iright
          iexists base
          iframe
          isplitr
          · ipureintro; exact Hpos
          · unfold mapCells; iexists bs; iframe; ipureintro; exact Hbs
  · obtain ⟨he, rfl⟩ := Hbe
    simp only [errnoErr, he, ↓reduceIte]
    wp_auto
    ihave Hfo : fileOwn f fd p dqo $$ [Hfo]
    · rw [fileOwn_eq]; iexact Hfo
    iapply HΦ
    iframe Hf Hfo Hfd
    iright
    iframe Hdr Hd Hsz
    have hS := hErr e he
    simp only [errnoErr, he, ↓reduceIte] at hS
    ihave #HeS := hS
    isplitr
    · ipureintro
      refine ⟨by simp [interface.mkOk], ?_⟩
      have := errPtrTyped_errno e
      unfold errnoErr at this; rw [if_neg he] at this; exact this
    · iframe HeS
      ileft; iexact Hm

end map

end bbolt
end EtcdGrove
end Perennial
