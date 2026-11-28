/-
**`io.SectionReader` and `io.CopyN`** (names only in Perennial; S4, 2026-11-18): the vocabulary of
their trust-boundary specs (`Spec/io/NewSectionReader.lean`, `Spec/io/CopyN.lean`), what bbolt's
`Tx.WriteTo` uses of them (tx.go: `io.CopyN(w, io.NewSectionReader(f, dataOffset, dataSize),
dataSize)`, `f` the database's `*os.File`). Lean-first (no Rocq counterpart).

* `io.secReader sr r off n` (exclusive): `sr` is a `*SectionReader` made by
  `NewSectionReader(r, off, n)` and not read yet: it reads `r`'s `ReadAt` from `off` up to
  `off + n` (Go's `SectionReader{r, off, off, off + n, n}`; the spec asks `off + n < 2^63`, so
  Go's overflow case, a limit of `MaxInt64`, does not arise). Only `CopyN`'s spec takes it, whole.
* `io.readerAtOk r P Hd` (persistent): the `io.ReaderAt` contract of `r`, by its client's resource
  `P` and a relation `Hd i x` (the byte at offset `i` may be `x`): `r.ReadAt(b, o)`, with `P`, at
  `0 ≤ o`, `len(b) ≤ 32 KiB` (`io.Copy`'s buffer) and `o + len(b) < 2^63`, returns `n` with
  `0 ≤ n ≤ len(b)` (as an unsigned `w64`, so `n` is not negative as an `int`) and the first `n`
  bytes of `b` related by `Hd` to the offsets `o, o + 1, ...`, keeping `P`; any well-typed error
  (`io.ptrTyped`: the copy compares it with `io.EOF`), which the copy does not inspect beyond `nil`
  and `io.EOF`. An `*os.File` has it from its racing read
  (`os.File.readerAtOk`, `Proof/os/ReaderAt.lean`).
* `io.writerPlain w` (pure; the spec plan's `writerPlain`, `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean`):
  `w`'s dynamic type has no `ReadFrom` method. `io.Copy` calls `dst.ReadFrom(src)` when `dst`
  implements `io.ReaderFrom`; without it, it loops over `Read` and `Write`, which is what the spec
  of `CopyN` describes. `*io.PipeWriter` has it (`io.writerPlain_pipeWriter`).
-/
module

public import Perennial.Proof.io
public import Perennial.Code.io
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section plain
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- See the file header. -/
def io.writerPlain (w : GoInterfaceOk) : Prop := methodSet w.ty !! go!"ReadFrom" = none

end plain

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`*io.PipeWriter` has no `ReadFrom`** (its method set: `Close`, `CloseWithError`, `Write`). -/
theorem io.writerPlain_pipeWriter [_root_.Perennial.io.PipeWriter.TypeAssumptions] (pw : val) :
    io.writerPlain ⟨go.GoType.PointerType _root_.Perennial.io.PipeWriter.ty, pw⟩ := by
  have h := go.method_set_is (t := go.GoType.PointerType _root_.Perennial.io.PipeWriter.ty)
    go!"ReadFrom"
  simp only [go.methodSetLookup] at h
  exact h

/-- **The `*SectionReader` `sr` of `r` from `off`, `n` bytes long** (exclusive; see the file
header): Go's `SectionReader{r, off, off, off + n, n}`, owned, at `0 ≤ off`, `0 ≤ n` and
`off + n < 2^63` (`NewSectionReader`'s premises). -/
def io.secReader (sr : Loc) (r : GoInterfaceOk) (off n : w64) : IProp GF :=
  iprop(⌜0 ≤ sint.Z off ∧ 0 ≤ sint.Z n ∧ off.toNat + n.toNat < 2 ^ 63⌝ ∗
    sr ↦ ({ r' := GoInterface.ok r, base' := off, off' := off, limit' := off + n, n' := n } :
      _root_.Perennial.io.SectionReader))

/-- **The `io.ReaderAt` `r`'s contract, by `P` and the byte relation `Hd`** (persistent; see the
file header). -/
def io.readerAtOk (r : GoInterfaceOk) (P : IProp GF) (Hd : Nat → w8 → Prop) : IProp GF :=
  iprop(□ ∀ (b : GoSlice) (vs : List w8) (o : w64),
    {{ ⌜0 ≤ sint.Z o ∧ vs.length ≤ 32768 ∧ o.toNat + vs.length < 2 ^ 63⌝ ∗ P ∗ b ↦* vs }}
      (App (App (Val #(methods r.ty go!"ReadAt" r.v)) (Val #b)) (Val #o))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        P ∗ ∃ vs' : List w8, b ↦* vs' ∗
          ⌜vs'.length = vs.length ∧ n.toNat ≤ vs.length ∧
            (∀ i x, vs'[i]? = some x → i < n.toNat → Hd (o.toNat + i) x) ∧
            _root_.Perennial.io.ptrTyped err⌝ }})

instance io.readerAtOk_persistent (r : GoInterfaceOk) (P : IProp GF) (Hd : Nat → w8 → Prop) :
    Persistent (io.readerAtOk r P Hd) := by
  unfold io.readerAtOk; infer_instance

/-- **The `io.Writer` `w`'s contract** (persistent; moved here from the backend's `InvSnapshot`,
whose `backend.writerOk` is this, session S4, so that bbolt's `Tx.WriteTo` and `io.CopyN` state it
without the backend), by `Wr c bs`, the bytes `bs` written so far (`c`: whether a `Write` has
returned): `Write(p)` of a slice holding `chunk` (read at `dq`, given back) appends the first `k`
bytes of `chunk` and returns `k`, all of them unless the error is non-nil; (session S4) its error is
one `fmt` formats (`fmtErrorOkOrNil`: bbolt's `Tx.WriteTo` wraps it with `fmt.Errorf`; a pipe's
writer returns `io.ErrClosedPipe`, its reader end being only closed, `io.rcCloseOk`). -/
def io.writerOk (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (dq : DFrac) (chunk bs : List w8) (c : Bool),
    {{ p ↦*{dq} chunk ∗ Wr c bs }}
      (App (Val #(methods w.ty go!"Write" w.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, p ↦*{dq} chunk ∗ Wr true (bs ++ chunk.take k) ∗
          ⌜sint.Z n = k ∧ k ≤ chunk.length ∧ (err = GoInterface.nil → k = chunk.length)⌝ ∗
          fmtErrorOkOrNil err }})

instance io.writerOk_persistent (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) :
    Persistent (io.writerOk w Wr) := by
  unfold io.writerOk; infer_instance

end defs

end EtcdGrove
end Perennial
