/-
`f.Read(b)` reading to the end of the file (W3/W5 of `notes/wal-fsext-plan.md`, branch `wal-read5`):
`Off.lean`'s `os.File.Read.wp_spec` asks the read to lie inside the file; a stream reader
(`io.readerStream`, the WAL's decoder through `bufio`) reads past the end too. Here the client holds
the whole file's bytes from 0 (any fractions) and its `OsMeta` (so the size is known): one `read(2)`
(`EINTR` retried) of at most `min(len(b), 1 GiB)` bytes at the offset, so a short read, `0, io.EOF` at
or past the end (for a non-empty `b`), `0, nil` for an empty `b`, or a `*PathError`. The read must end
below `2^62` (`model.offMax`). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.Off
public import LinuxFs.Proof.os.ErrorOk
public import LinuxFs.Proof.os.ErrnoPathErr

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

/-- The bytes `[o, o + n)` of a file held from 0 (empty past the end), and the rest back. -/
theorem os.osBytes_mid (i : Ino) (dq : DFrac) (bs : List ByteG) (o n : Nat) :
    osBytes (GF := GF) i 0 dq bs ⊢
      osBytes (GF := GF) i o dq ((bs.drop o).take n) ∗
        (osBytes (GF := GF) i o dq ((bs.drop o).take n) -∗ osBytes (GF := GF) i 0 dq bs) := by
  by_cases ho : o ≤ bs.length
  · have e : bs = bs.take o ++ ((bs.drop o).take n ++ (bs.drop o).drop n) := by
      rw [List.take_append_drop, List.take_append_drop]
    have hl : 0 + (bs.take o).length = o := by simp only [List.length_take]; omega
    have A1 := bytesG_append (gooseOsGS (GF := GF)) i dq 0 (bs.take o)
      ((bs.drop o).take n ++ (bs.drop o).drop n)
    rw [hl] at A1
    have A2 := bytesG_append (gooseOsGS (GF := GF)) i dq o ((bs.drop o).take n) ((bs.drop o).drop n)
    unfold osBytes
    conv => lhs; rw [e]
    refine A1.1.trans ((sep_mono .rfl A2.1).trans ?_)
    iintro ⟨H1, H2, H3⟩
    iframe H2
    iintro H2
    conv => rhs; rw [e]
    iapply A1.2
    iframe H1
    iapply A2.2
    iframe
  · have hd : (bs.drop o).take n = [] := by
      rw [List.drop_eq_nil_of_le (by omega)]; simp
    rw [hd]
    iintro H
    isplitr
    · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
    iintro -
    iexact H

set_option hygiene false in
/-- The rest of `Read` once the `pread` length `N` is known (`hNl`; `hd` rewrites the length's
test as the case split did). -/
local macro "read_rest " N:term:max hd:term:max : tactic => `(tactic| (
  obtain ⟨Nn, hNn⟩ : ∃ Nn, ($N).toNat = Nn := ⟨_, rfl⟩
  rw [hNn] at hNl
  ihave ⟨Hmid, Hback⟩ := os.osBytes_mid d.ino dqb bs o.toNat Nn $$ Hbs
  wp_apply wp_osPRead fd o ($N) dq dqm dqb d m ((bs.drop o.toNat).take Nn)
    CoPset.subseteq_top hrd h0 (by rw [hNn]; simp only [List.length_take, List.length_drop]; omega)
    $$ Hinv Hosfd Hm Hmid as %r %e %hre Hosfd Hm Hmid
  ihave Hbs := Hback $$ Hmid
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    rw [($hd:term)]
    iapply IH $$ Hosfd Hm Hbs Hsl Ho Hfd HΦ
  rw [decide_eq_false he4]
  wp_auto
  obtain ⟨k, hkl, rfl, hke0⟩ := hre
  simp only [List.length_take, List.length_drop] at hkl
  by_cases he0 : e = W64 0
  rotate_left
  · simp only [decide_eq_false he0, Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno_errno _ inner name e $$ Hn as %perr #Hep
    ihave #Hok := os.errnoPathErr_fmtErrorOk perr e he0 $$ Hep
    ihave #Hep2 := Hep
    iunfold os.errnoPathErr at Hep2
    icases Hep2 with ⟨%pe, %op, %path, %hpe, -⟩
    subst hpe
    iapply HΦ
    iframe Hosfd Hm Hbs
    isplitl [Hfd]
    · iexists inner; iframe; isplitl [] <;> iassumption
    iexists 0
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    iframe Hsl
    isplitr
    · ipureintro; exact ⟨by first | rfl | trivial, Nat.zero_le _, Nat.zero_le _⟩
    isplitl [Ho]
    · rw [show o + W64 (0 : Nat) = o by simp]; iexists inner; iframe Ho; iassumption
    iright; iright
    isplitr
    · ipureintro; first | rfl | trivial
    iexists pe; iframe Hok
    isplitr
    · ipureintro; first | rfl | trivial
    iexists e; iframe Hep; ipureintro; exact he0
  subst he0
  rw [show decide ((W64 0) = W64 0) = true from decide_eq_true rfl]
  simp only [Bool.not_true]
  wp_auto
  have hrw : ((bs.drop o.toNat).take Nn).map Prod.fst =
      ((bs.map Prod.fst).drop o.toNat).take Nn := by
    rw [List.map_take, List.map_drop]
  rw [hrw]
  have hkN : k ≤ Nn := by omega
  have hrk : (((bs.map Prod.fst).drop o.toNat).take Nn).take k =
      ((bs.map Prod.fst).drop o.toNat).take k := by
    rw [List.take_take, Nat.min_eq_left hkN]
  rw [hrk]
  have hrl : (((bs.map Prod.fst).drop o.toNat).take k).length = k := by
    simp only [List.length_take, List.length_drop, List.length_map]; omega
  have hkv : k ≤ vs.length := by omega
  wp_apply wp_string_to_bytes (((bs.map Prod.fst).drop o.toNat).take k) as %tmp ⟨Htmp, -⟩
  by_cases hk0 : k = 0
  · subst hk0
    icases ownSlice_len tmp _ _ $$ Htmp with %Htl
    have htl0 : tmp.len = W64 0 := by
      apply BitVec.eq_of_toInt_eq
      simp only [List.take_zero, List.length_nil, sint.nat, sint.Z] at Htl
      rw [show (W64 0).toInt = 0 from rfl]; omega
    wp_apply wp_slice_copy_of_len_zero sl tmp htl0
    try wp_auto
    have hv0 : vs.length ≠ 0 := fun h => hl0 (by rw [hsl, h]; rfl)
    have hend : bs.length ≤ o.toNat := by
      rcases hke0 rfl with h | h
      · omega
      · have := congrArg List.length h
        simp only [List.length_take, List.length_drop, List.length_nil] at this
        omega
    iapply HΦ
    iframe Hosfd Hm Hbs
    isplitl [Hfd]
    · iexists inner; iframe; isplitl [] <;> iassumption
    iexists 0
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    iframe Hsl
    isplitr
    · ipureintro; exact ⟨by first | rfl | trivial, Nat.zero_le _, Nat.zero_le _⟩
    isplitl [Ho]
    · iexists inner; iframe Ho; iassumption
    iright; ileft; ipureintro
    refine ⟨by first | rfl | trivial, fun h => hv0 (by rw [h]; rfl), hend, ?_⟩
    first | rfl | trivial
  wp_apply wp_slice_copy sl vs tmp (((bs.map Prod.fst).drop o.toNat).take k) (DFrac.own 1)
    $$ [Hsl Htmp] as %mm ⟨%hmm, Hsl, -⟩
  · iframe
  have hmmv : sint.nat mm = k := by rw [hmm, hrl]; omega
  have hmmeq : mm = W64 k := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.nat, sint.Z] at hmmv
    rw [show (W64 (k : Int)).toInt = k by
      rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega]
    omega
  subst hmmeq
  rw [List.take_of_length_le (by rw [hrl]; omega), hrl]
  have hk0' : ¬ (W64 (k : Int)) = W64 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofInt] at this; omega
  rw [decide_eq_false hk0']
  wp_auto
  iapply HΦ
  iframe Hosfd Hm Hbs
  isplitl [Hfd]
  · iexists inner; iframe; isplitl [] <;> iassumption
  iexists k
  iframe Hsl
  isplitr
  · ipureintro; exact ⟨by first | rfl | trivial, hkv, by omega⟩
  isplitl [Ho]
  · iexists inner; iframe Ho; iassumption
  ileft; ipureintro; exact ⟨by first | rfl | trivial, .inl (by omega)⟩))

/-- `f.Read(b)` at the offset `o` of a file whose bytes the client holds from 0 (`bs`, the whole
file: `|bs| = size`), any fractions, the read ending below `2^62`: it delivers the `k` bytes from
`o` on (`k ≤ len(b)`, `o + k ≤ size`) into the front of `b`, moving the offset by `k`; with `nil`,
`k > 0` unless `b` is empty; `0, io.EOF` only at or past the end of the file; or `0` and a
`*PathError` of a nonzero errno (`os.errnoPathErr`). -/
theorem os.File.Read.wp_eof (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (vs : List w8) (o : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta) (bs : List ByteG)
    (eof : GoInterface)
    (hfd : 0 ≤ fd.toInt) (hrd : d.readable = true) (h0 : 0 ≤ o.toInt) (hbs : bs.length = m.size)
    (hmax : o.toInt + vs.length < 2 ^ 62) :
    {{ osInv (GF := GF) ∗ globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
        os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        sl ↦* vs ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino dqm m ∗
        osBytes (GF := GF) d.ino 0 dqb bs }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Read")) (Val #sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.ino dqm m ∗ osBytes d.ino 0 dqb bs ∗
        ∃ k : Nat, ⌜n = W64 k ∧ k ≤ vs.length ∧ k ≤ bs.length - o.toNat⌝ ∗
          sl ↦* (((bs.map Prod.fst).drop o.toNat).take k ++ vs.drop k) ∗ os.ownOff f (o + W64 k) ∗
          (⌜err = interface.nil ∧ (0 < k ∨ vs = [])⌝ ∨
           ⌜k = 0 ∧ vs ≠ [] ∧ bs.length ≤ o.toNat ∧ err = eof⌝ ∨
           (⌜k = 0⌝ ∗ ∃ pe : Loc,
              ⌜err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ ∗
              fmtErrorOk err ∗ ∃ e : w64, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e)) }} := by
  unfold os.ownFile os.ownOff
  wp_start as ⟨#Hinv, #Heof, ⟨%inner, #Hf, Hfd, #Hn⟩, ⟨%inner', #Hf', Ho⟩, Hsl, Hosfd, Hm, Hbs⟩
  icombine Hf Hf' gives %hin'
  cases hin'
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z fd < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd)]
  wp_auto
  by_cases hl0 : sl.len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    have hv : vs = [] := by
      rw [hl0, show sint.Z (W64 0) = 0 from rfl] at hslz
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hv
    iapply HΦ
    iframe Hosfd Hm Hbs
    isplitl [Hfd]
    · iexists inner; iframe; isplitl [] <;> iassumption
    iexists 0
    simp only [List.take_zero, List.drop_zero, List.nil_append, List.length_nil]
    iframe Hsl
    isplitr
    · ipureintro; exact ⟨rfl, Nat.le_refl _, Nat.zero_le _⟩
    isplitl [Ho]
    · rw [show o + W64 (0 : Nat) = o by simp]; iexists inner; iframe Ho; iassumption
    ileft; ipureintro; simp
  rw [decide_eq_false hl0]
  wp_auto
  have hsl : sl.len = W64 vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
  rw [decide_eq_false (show ¬ sint.Z o < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega)]
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl]
  try wp_auto
  have hsum : sint.Z (o + sl.len) = o.toInt + vs.length := by
    rw [hsl]; simp only [sint.Z]; word
  rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (o + sl.len) by
    rw [hsum, show sint.Z (W64 0x4000000000000000) = 2 ^ 62 from rfl]; omega)]
  wp_auto
  iloeb as IH generalizing Hosfd Hm Hbs Hsl Ho Hfd HΦ
  by_cases hmx : sint.Z (W64 1073741824) < sint.Z sl.len
  · rw [decide_eq_true hmx]
    wp_auto
    have hNl : (W64 1073741824).toNat = min vs.length 1073741824 := by
      rw [hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl] at hmx
      rw [Nat.min_eq_right (by omega)]; rfl
    read_rest (W64 1073741824) (decide_eq_true hmx)
  · rw [decide_eq_false hmx]
    wp_auto
    have hNl : sl.len.toNat = min vs.length 1073741824 := by
      rw [hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl] at hmx
      rw [Nat.min_eq_left (by omega), hsl]
      simp only [BitVec.toNat_ofInt]; omega
    read_rest sl.len (decide_eq_false hmx)

end proof

end EtcdGrove
end Perennial
