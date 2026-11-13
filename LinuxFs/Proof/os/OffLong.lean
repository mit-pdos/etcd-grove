/-
`(*os.File).Write` of any length (`Off.lean`'s `os.File.Write.wp_spec` takes 1 byte to 1 GiB), over
`WriteAt`'s spec of any length (`os.File.WriteAt.specLong`, `Spec/os/WriteLong.lean`), and of an
empty slice (`os.File.Write.wp_empty`: the model's empty-`Write` branch, no extension step, the
offset unchanged, nil or an error). On an error the model returns any count and loses the offset
(`-1`), so the post says nothing of the count; the file is as the `WriteAt` that failed left it.
WAL W6 (2026-11-13, `wal-bridge`). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.Off
public import LinuxFs.Spec.os.WriteLong

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `PwOutA` with everything announced is `PwOut`. -/
theorem os.PwOutA.pwOut {m : OsMeta} {off : Nat} {data : List w8} {j : Nat} {xs ys : List ByteG}
    (h : os.PwOutA m off data data.length j xs ys) : os.PwOut m off data j xs ys := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨h1, c0, extra, h2, h3, h4, h5⟩ := h.2 i hi
  have : i < data.length := by have := h.1; omega
  exact ⟨h1, c0, extra, h2, h3 this, h4, h5⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- `f.Write(b)` of an empty `b` on an open fd: `(0, nil)` or `(0, err)`, the offset unchanged,
nothing else touched (the model's empty-`Write` branch). -/
theorem os.File.Write.wp_empty (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (dqs : DFrac) (o : w64) (hfd : 0 ≤ fd.toInt) :
    {{ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗ sl ↦*{dqs} ([] : List w8) }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Write")) (Val #sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ⌜n = W64 0⌝ ∗ os.ownFile f fd name dqf ∗ os.ownOff f o ∗ sl ↦*{dqs} ([] : List w8) }} := by
  unfold os.ownOff
  wp_start as ⟨Hf, ⟨%inner, #Hfi, Ho⟩, Hsl⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hfi
  iStructNamed Hf2
  icases ownSlice_len sl _ ([] : List w8) $$ Hsl with %Hlen
  iunfold os.ownFile at Hf
  icases Hf with ⟨%inner0, #Hf0, Hfd0, #Hn0⟩
  icombine Hfi Hf0 gives %hin0
  cases hin0
  wp_auto
  have hsl : sl.len = W64 0 := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z, List.length_nil] at h1 h2; word
  rw [decide_eq_false (show ¬ sint.Z fd < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd)]
  wp_auto
  rw [hsl, decide_eq_true (rfl : W64 0 = W64 0)]
  wp_auto
  wp_apply wp_ArbitraryInt as %e _
  ihave Hf : os.ownFile f fd name dqf $$ [Hfd0]
  · unfold os.ownFile; iexists inner; iframe; isplitl [] <;> iassumption
  by_cases he : e = W64 0
  · subst he
    rw [decide_eq_true (rfl : W64 0 = W64 0)]
    wp_auto
    iapply HΦ
    iframe Hf Hsl
    isplitr
    · ipureintro; rfl
    iexists inner; iframe; iassumption
  · rw [decide_eq_false he]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn0 as %pe
    iapply HΦ
    iframe Hf Hsl
    isplitr
    · ipureintro; rfl
    iexists inner; iframe; iassumption

/-- `f.Write(b)` of a non-empty `b` of any length on an open fd at the offset `o` (`0 ≤ o ≤ size`,
`o + len(b) < 2^62`), over `WriteAt`'s spec of any length at `o`: on success `len(b)`, the offset
past `b`, the file as a write of all of `b` left it (`PwOut`, `pwPost`); on an error any count, the
offset unknown (`-1`), the file as `WriteAt`'s failure left it. -/
theorem os.File.Write.wp_long (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (o : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hfd : 0 ≤ fd.toInt) (hwr : d.writable = true) (h0 : 0 ≤ o.toInt) (hle : o.toNat ≤ m.size)
    (hlo : m.lo ≤ m.size) (hn : 0 < data.length)
    (hxs : xs.length = min (o.toNat + data.length) m.size - o.toNat)
    (hmax : o.toInt + data.length < 2 ^ 62) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
        osBytes (GF := GF) d.ino o.toNat (DFrac.own 1) xs ∗
        mcellsAny (GF := GF) m.maps o.toNat (o.toNat + data.length) }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Write")) (Val #sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
        mcellsAny m.maps o.toNat (o.toNat + data.length) ∗
        ((∃ ys : List ByteG, ⌜err = interface.nil ∧ n = W64 data.length ∧
              os.PwOut m o.toNat data data.length xs ys⌝ ∗
            osMeta d.ino (DFrac.own 1) (pwPost m o.toNat data.length data.length) ∗
            osBytes d.ino o.toNat (DFrac.own 1) ys ∗ os.ownOff f (o + W64 data.length)) ∨
         (∃ (j A : Nat) (ys : List ByteG), ⌜err ≠ interface.nil ∧ j ≤ A ∧ A ≤ data.length ∧
              os.PwOutA m o.toNat data A j xs ys ∧ PwCut o.toNat data.length j⌝ ∗
            osMeta d.ino (DFrac.own 1) (pwPost m o.toNat A j) ∗
            osBytes d.ino o.toNat (DFrac.own 1) ys ∗ os.ownOff f (W64 (-1)))) }} := by
  unfold os.ownOff
  wp_start as ⟨#Hinv, Hf, ⟨%inner, #Hfi, Ho⟩, Hsl, Hosfd, Hm, Hbs, Hmc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hfi
  iStructNamed Hf2
  icases ownSlice_len sl _ data $$ Hsl with %Hlen
  iunfold os.ownFile at Hf
  icases Hf with ⟨%inner0, #Hf0, Hfd0, #Hn0⟩
  icombine Hfi Hf0 gives %hin0
  cases hin0
  wp_auto
  have hsl : sl.len = W64 data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
  rw [decide_eq_false (show ¬ sint.Z fd < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd)]
  wp_auto
  rw [decide_eq_false (show ¬ sl.len = W64 0 by
    rw [hsl]; intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofInt] at this; omega)]
  wp_auto
  ihave Hf : os.ownFile f fd name dqf $$ [Hfd0]
  · unfold os.ownFile; iexists inner; iframe; isplitl [] <;> iassumption
  rw [decide_eq_false (show ¬ sint.Z o < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega)]
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl, hsl]
  try wp_auto
  have hsum : sint.Z (o + W64 (data.length : Int)) = o.toInt + data.length := by
    simp only [sint.Z]; word
  rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (o + W64 (data.length : Int)) by
    rw [hsum, show sint.Z (W64 0x4000000000000000) = 2 ^ 62 from rfl]; omega)]
  wp_auto
  have h63 : o.toNat + data.length < 2 ^ 63 := by
    have := BitVec.toInt_eq_toNat_cond o; split at this <;> omega
  wp_apply wp_WriteAt f fd name dqf sl data dqs o dq d m xs hwr h0 hle h63 hn hlo hxs
    $$ [Hinv Hf Hsl Hosfd Hm Hbs Hmc] as %n %err ⟨Hf, Hsl, Hosfd, %j, %A, %ys, %Hres, Hm, Hbs, Hmc, -⟩
  · iframe; iexact Hinv
  obtain ⟨hjA, hAn, -, hout, hcut, hr⟩ := Hres
  cases err with
  | nil =>
    rcases hr with ⟨rfl, rfl, -⟩ | ⟨-, h⟩
    rotate_left
    · exact absurd rfl h
    have hA : A = data.length := by omega
    subst hA
    wp_auto
    iapply HΦ
    iframe Hf Hsl Hosfd Hmc
    ileft
    iexists ys
    iframe Hm Hbs
    isplitr
    · ipureintro; exact ⟨rfl, rfl, os.PwOutA.pwOut hout⟩
    iexists inner; iframe; iassumption
  | ok ie =>
    wp_auto
    wp_apply wp_ArbitraryInt as %x _
    iapply HΦ
    iframe Hf Hsl Hosfd Hmc
    iright
    iexists j, A, ys
    iframe Hm Hbs
    isplitr
    · ipureintro; exact ⟨fun h => (nomatch h), hjA, hAn, hout, hcut⟩
    iexists inner; iframe; iassumption

end proof

end EtcdGrove
end Perennial
