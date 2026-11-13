/-
`f.Seek(off, io.SeekEnd)` with an offset (`Off.lean`'s `wp_end` is `off = 0`): `fileutil`'s
`preallocExtendTrunc` seeks `sizeInBytes` past the end. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.Off

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
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- `f.Seek(off, io.SeekEnd)`, `0 ≤ off`, the size and `off` at most ext4's maximum (`seekMax`):
the offset becomes `size + off` if that is at most the maximum; else (or on an `fstat` error) an
error, the offset unchanged. -/
theorem os.File.Seek.wp_endOff (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (o off : w64)
    (dq dqm : DFrac) (d : OsFd) (m : OsMeta) (hfd : 0 ≤ fd.toInt) (hsz : m.size ≤ 0xffffffff000)
    (h0 : 0 ≤ off.toInt) (hoff : off.toInt ≤ 0xffffffff000) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino dqm m }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Seek")) (Val #off))
        (Val #(W64 2)))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); os.ownFile f fd name dqf ∗
        osFd fd dq d ∗ osMeta d.ino dqm m ∗
        ((⌜n = W64 m.size + off ∧ m.size + off.toNat ≤ 0xffffffff000 ∧ err = interface.nil⌝ ∗
            os.ownOff f (W64 m.size + off)) ∨
         (⌜err ≠ interface.nil⌝ ∗ os.ownOff f o)) }} := by
  unfold os.ownFile os.ownOff
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, ⟨%inner', #Hf', Ho⟩, Hosfd, Hm⟩
  icombine Hf Hf' gives %hin
  cases hin
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  have hfd' : ¬ sint.Z fd < sint.Z (W64 0) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd
  rw [decide_eq_false hfd']
  wp_auto
  wp_apply wp_osFstat fd dq dqm d m CoPset.subseteq_top $$ Hinv Hosfd Hm as %sz %e %hr Hosfd Hm
  rcases hr with ⟨rfl, rfl⟩ | ⟨he, rfl⟩
  · rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    rw [show os.model.offMax = W64 0x4000000000000000 from rfl,
      show os.model.seekMax = W64 0xffffffff000 from rfl]
    have hm : sint.Z (W64 0x4000000000000000) = 2 ^ 62 := rfl
    have hs : sint.Z (W64 (m.size : Int)) = m.size := by
      show BitVec.toInt _ = _
      rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
    have ho : sint.Z off = off.toInt := rfl
    have hn : sint.Z (W64 (m.size : Int) + off) = m.size + off.toInt := by
      have : (off.toInt) ≤ 0xffffffff000 := hoff
      word
    have hz : sint.Z (W64 0) = 0 := rfl
    have hS : sint.Z (W64 0xffffffff000) = 0xffffffff000 := rfl
    rw [decide_eq_false (show ¬ sint.Z (W64 (m.size : Int) + off) < sint.Z (W64 0) by
      rw [hn, hz]; omega)]
    wp_auto
    try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (W64 (m.size : Int) + off) by
      rw [hm, hn]; omega)]
    try wp_auto
    try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (W64 (m.size : Int)) by
      rw [hm, hs]; omega)]
    try wp_auto
    try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z off by
      rw [hm, ho]; omega)]
    try wp_auto
    by_cases hbig : 0xffffffff000 < m.size + off.toInt
    · rw [decide_eq_true (show sint.Z (W64 0xffffffff000) < sint.Z (W64 (m.size : Int) + off) by
        rw [hS, hn]; omega)]
      wp_auto
      wp_apply os.wp_wrapErrno _ inner name (W64 22) $$ Hn as %pe
      iapply HΦ
      iframe Hosfd Hm
      isplitl [Hfd]
      · iexists inner; iframe; isplitl [] <;> iassumption
      · iright
        isplitr
        · ipureintro; intro h; cases h
        iexists inner; iframe; iassumption
    · rw [decide_eq_false (show ¬ sint.Z (W64 0xffffffff000) < sint.Z (W64 (m.size : Int) + off) by
        rw [hS, hn]; omega)]
      wp_auto
      iapply HΦ
      iframe Hosfd Hm
      isplitl [Hfd]
      · iexists inner; iframe; isplitl [] <;> iassumption
      · ileft
        isplitr
        · ipureintro
          refine ⟨rfl, ?_, rfl⟩
          have : (off.toNat : Int) = off.toInt := by
            have := BitVec.toInt_eq_toNat_cond off; split at this <;> omega
          omega
        iexists inner; iframe; iassumption
  · have he' : ¬ e = W64 0 := he
    simp only [decide_eq_false he', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iframe Hosfd Hm
    isplitl [Hfd]
    · iexists inner; iframe; isplitl [] <;> iassumption
    · iright
      isplitr
      · ipureintro; intro h; cases h
      iexists inner; iframe; iassumption

end proof

end EtcdGrove
end Perennial
