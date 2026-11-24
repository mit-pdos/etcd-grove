/-
**A `*bufio.Reader` to be reset** (net/http's server, 2026-11-23: the readers of its pool,
`newBufioReader`): `bufio.rawReader b` is the reader's struct with a buffer of `1` to `4096` bytes,
its other fields any; `bufio.freshReader b rd` is the same after `Reset(rd)`: reading from `rd`,
nothing buffered, no pending error. `bufio.freshReader_own`: a fresh reader over a stream reader in
the state `S r` is `bufio.ownReader` (`Proof/bufio/Defs.lean`) at `r`. Lean-first.
-/
module

public import Proof.bufio.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
def bufio.rawReader (b : Loc) : IProp GF :=
  iprop(∃ (v : _root_.Perennial.bufio.Reader) (bs : List w8), b ↦ v ∗ v.buf' ↦* bs ∗
    ⌜0 < bs.length ∧ bs.length ≤ 2 ^ 12⌝)

/-- See the file header. -/
def bufio.freshReader (b : Loc) (rd : GoInterface) : IProp GF :=
  iprop(∃ (v : _root_.Perennial.bufio.Reader) (bs : List w8), b ↦ v ∗ v.buf' ↦* bs ∗
    ⌜v.rd' = rd ∧ v.r' = W64 0 ∧ v.w' = W64 0 ∧ v.err' = interface.nil ∧
      0 < bs.length ∧ bs.length ≤ 2 ^ 12⌝)

theorem bufio.freshReader_raw (b : Loc) (rd : GoInterface) :
    bufio.freshReader (GF := GF) b rd ⊢ bufio.rawReader b := by
  unfold bufio.freshReader bufio.rawReader
  iintro ⟨%v, %bs, Hb, Hbuf, %Hv⟩
  iexists v, bs
  iframe Hb Hbuf
  ipureintro; exact ⟨Hv.2.2.2.2.1, Hv.2.2.2.2.2⟩

/-- See the file header. -/
theorem bufio.freshReader_own (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r : List w8) :
    isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ bufio.freshReader b (GoInterface.ok ri) ∗ S r ⊢
      bufio.ownReader b ri S E r := by
  unfold bufio.freshReader bufio.ownReader
  iintro ⟨#Hpkg, ⟨%v, %bs, Hb, Hbuf, %Hv⟩, HS⟩
  obtain ⟨hrd, hr, hw, herr, hpos, hle⟩ := Hv
  iframe Hpkg
  iexists v, bs
  have hsub : subslice (sint.nat v.r') (sint.nat v.w') bs = [] := by
    rw [hr, hw]; simp [subslice_def]
  rw [hsub, List.append_nil, herr]
  iframe Hb Hbuf HS
  isplitr
  · ipureintro
    rw [hr, hw]
    exact ⟨hrd, by decide, by decide, by simp, hpos, hle⟩
  unfold io.errAt
  isplitl
  · ileft; ipureintro; rfl
  · ipureintro; exact _root_.Perennial.io.ptrTyped_nil

end defs

end EtcdGrove
end Perennial
