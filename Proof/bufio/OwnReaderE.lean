/-
**The WAL's `bufio.ownReader` as a generic buffered reader** (dsv-bufio, review R1 on #24): the
WAL's reader (`bufio.ownReader b ri S E r`, `Proof/bufio/Defs.lean`, over the stream reader
`io.readerStream ri S E`) is `bufio.ownBufReaderE` (`Proof/bufio/Own.lean`) at the condition
`bufio.walPre` on each read (`r.length + m < 2^62`, `io.readerStream_readerOk`), the evidence `E` of
its errors (it never calls `fill`, so never returns `io.ErrNoProgress`) and buffers of at most 4096
bytes, given the stream reader and its states' bound (`□ ∀ r', S r' -∗ ⌜r'.length + 2^12 < 2^62⌝`):
`bufio.ownReader_toE` and back, `bufio.ownReader_ofE`. So the WAL's `bufio.NewReader.spec` and
`bufio.Reader.Read.spec` are proved from the one proof of `NewReaderSize` and of `Read`
(`bufio.NewReaderSize.specE`, `bufio.Reader.Read.specE`), not by proofs of their own.
Lean-first.
-/
module

public import Proof.bufio.Defs
public import Proof.bufio.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section pure

/-- The WAL's condition on each read of its stream reader (`io.readerStream_readerOk`). -/
def bufio.walPre : List w8 → Nat → Prop := fun r m => r.length + m < 2 ^ 62

/-- A buffer split at `r ≤ w`: before, between, after. -/
theorem bufio.split_subslice {α : Type} (r w : Nat) (bs : List α) (h : r ≤ w) :
    bs.take r ++ subslice r w bs ++ bs.drop w = bs := by
  rw [subslice_def, show bs.take r = (bs.take w).take r by
    rw [List.take_take, Nat.min_eq_left h], List.take_append_drop, List.take_append_drop]

theorem bufio.subslice_mid {α : Type} (pre pend post : List α) :
    subslice pre.length (pre.length + pend.length) (pre ++ pend ++ post) = pend := by
  rw [subslice_def, List.append_assoc, List.take_append, List.take_of_length_le (by omega),
    show pre.length + pend.length - pre.length = pend.length by omega, List.take_append,
    List.take_of_length_le (Nat.le_refl _), Nat.sub_self, List.take_zero, List.append_nil,
    List.drop_left]

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- The WAL's errors: the stream's evidence, well typed (`io.errAt` of `Proof/io/ReaderStream.lean`),
from Perennial's `io.errAt` and `io.ptrTyped`. -/
theorem bufio.walErrAt_of (E : List w8 → GoInterface → IProp GF) (r : List w8) (e : GoInterface)
    (h : _root_.Perennial.io.ptrTyped e) :
    _root_.Perennial.io.errAt E r e ⊢ _root_.Perennial.EtcdGrove.io.errAt E r e := by
  unfold _root_.Perennial.io.errAt _root_.Perennial.EtcdGrove.io.errAt
  iintro #H
  iframe H
  ipureintro; exact h

theorem bufio.walErrAt_to (E : List w8 → GoInterface → IProp GF) (r : List w8) (e : GoInterface) :
    _root_.Perennial.EtcdGrove.io.errAt E r e ⊢
      _root_.Perennial.io.errAt E r e ∗ ⌜_root_.Perennial.io.ptrTyped e⌝ := by
  unfold _root_.Perennial.io.errAt _root_.Perennial.EtcdGrove.io.errAt
  iintro ⟨#H, %h⟩
  iframe H
  ipureintro; exact h

/-- See the file header. -/
theorem bufio.ownReader_toE (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r : List w8) :
    io.readerStream ri S E ∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) ∗
        bufio.ownReader b ri S E r ⊢
      bufio.ownBufReaderE b ri bufio.walPre S E E (· ≤ 2 ^ 12) r := by
  iintro ⟨#Hrs, #Hbd, Hown⟩
  ihave #Hrd := io.readerStream_readerOk ri S E $$ Hrs
  unfold bufio.ownReader
  icases Hown with ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, #Herr⟩
  obtain ⟨hrd, h0r, hrw, hwl, hpos, hle⟩ := Hwf
  ihave ⟨#Herr', %hty⟩ := bufio.walErrAt_to E _ _ $$ Herr
  cases v with
  | mk buf rd vr vw verr lb lrs =>
  simp only at hrd h0r hrw hwl hty
  subst hrd
  have hsplit := bufio.split_subslice (sint.nat vr) (sint.nat vw) bs (by
    show (sint.Z vr).toNat ≤ (sint.Z vw).toNat; omega)
  unfold bufio.ownBufReaderE bufio.readerRep
  iframe Hpkg
  isplitr
  · unfold bufio.walPre; iexact Hrd
  iexists subslice (sint.nat vr) (sint.nat vw) bs, verr
  iframe HS
  iexists buf, vr, vw, lb, lrs, bs.take (sint.nat vr), bs.drop (sint.nat vw)
  rw [hsplit]
  iframe Hv Hbuf Herr'
  isplitr
  · ipureintro
    have hwn : sint.nat vw = (sint.Z vw).toNat := rfl
    have hn : sint.nat vr ≤ bs.length := by show (sint.Z vr).toNat ≤ _; omega
    refine ⟨?_, ?_, hpos, hle, hty⟩
    · rw [List.length_take, Nat.min_eq_left hn]; show sint.Z vr = ((sint.Z vr).toNat : Int); omega
    · rw [List.length_take, Nat.min_eq_left hn, subslice_def, List.length_drop, List.length_take,
        Nat.min_eq_left hwl]
      show sint.Z vw = ((sint.Z vr).toNat : Int) + ((sint.Z vw).toNat - (sint.Z vr).toNat : Nat)
      omega
  unfold bufio.preUpTo bufio.walPre
  iintro !> %r' HS'
  ihave %h := Hbd $$ HS'
  ipureintro
  intro m _ hm
  omega

/-- See the file header. -/
theorem bufio.ownReader_ofE (b : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) (r : List w8) :
    bufio.ownBufReaderE b ri Pre S E E (· ≤ 2 ^ 12) r ⊢ bufio.ownReader b ri S E r := by
  unfold bufio.ownBufReaderE bufio.readerRep
  iintro ⟨#Hpkg, -, %pend, %perr, HS, %buf, %vr, %vw, %lb, %lrs, %pre, %post, Hb, Hbuf, %Hrw, -,
    #Herr⟩
  obtain ⟨hr, hw, hpos, hle, hty⟩ := Hrw
  ihave #Herr' := bufio.walErrAt_of E _ _ hty $$ Herr
  have hnr : sint.nat vr = pre.length := by show (sint.Z vr).toNat = _; omega
  have hnw : sint.nat vw = pre.length + pend.length := by show (sint.Z vw).toNat = _; omega
  have hsub : subslice (sint.nat vr) (sint.nat vw) (pre ++ pend ++ post) = pend := by
    rw [hnr, hnw]; exact bufio.subslice_mid pre pend post
  unfold bufio.ownReader
  iframe Hpkg
  iexists _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) vr vw perr lb lrs,
    pre ++ pend ++ post
  simp only
  rw [hsub]
  iframe Hb Hbuf HS Herr'
  ipureintro
  simp only [List.length_append] at hpos hle ⊢
  refine ⟨trivial, by omega, by omega, by omega, hpos, hle⟩

end laws

end EtcdGrove
end Perennial
