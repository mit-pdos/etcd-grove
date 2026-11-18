/-
`io.CopyN(w, sr, n)` of a fresh `*SectionReader` (names only in Perennial, with its callees `Copy`,
`copyBuffer`, `LimitReader`, `(*LimitedReader).Read` and `(*SectionReader).Read`; S4, 2026-11-18):
the trust boundary (an axiom in `Proof/io/CopyN.lean`), stated over the section reader
(`io.secReader`), the contract of its `io.ReaderAt` (`io.readerAtOk`), the writer's (`backend.writerOk`,
`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvSnapshot.lean`, as `io.Pipe`'s writer has it) and
`io.writerPlain` (`Proof/io/SectionReader.lean`). bbolt's `Tx.WriteTo` (tx.go) copies its data pages
this way. Lean-first.

Go 1.27's `io.go`, which the spec describes: `CopyN` is `Copy(dst, LimitReader(src, n))`, then
`(n, nil)` if all `n` came, else what `Copy` returned with `io.EOF` for a `nil` error. `Copy` is
`copyBuffer(dst, src, nil)`: a `*LimitedReader` has no `WriteTo`, and `dst` no `ReadFrom`
(`writerPlain`), so it loops over a buffer of `min(32 KiB, max(n, 1))` bytes: `nr, er :=
src.Read(buf)` (the limited reader truncates to what is left of `n`, the section reader to what
is left of the section, and reads `ReadAt(p, off + read so far)`); if `nr > 0`, `nw, ew :=
dst.Write(buf[0:nr])`, `written += nw`, and stop on `ew != nil` or `nw != nr`; stop on `er != nil`.
The writer's contract gives `0 ≤ nw ≤ nr` (no `errInvalidWrite`), and the reader's `0 ≤ nr ≤
len(buf)` (no panic slicing `buf[0:nr]`); every read but the last is written whole, so the bytes
written are those of the section from `off` on, in order.
-/
module

public import Proof.io.SectionReader
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `io.CopyN(w, sr, n)`, for a writer `w` without `ReadFrom` (`writerPlain`) whose contract
(`writerOk`) is at `Wr c bs₀`, and a fresh section reader `sr` of `r` from `off`, `n` bytes long,
whose `ReadAt` contract (`readerAtOk r P Hd`) is at `P`: writes some `bs` (`Wr c' (bs₀ ++ bs)`,
`c'` true if a `Write` returned, else `c`, with nothing written), at most `n` bytes, each related
by `Hd` to its offset in the reader (`off + j`), and returns `len(bs)` and an error that is `nil`
exactly when all `n` bytes were written. It may not return (a `ReadAt` that keeps returning `0,
nil`: partial correctness). -/
abbrev io.CopyN.spec : Prop :=
  ∀ (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) (c : Bool) (bs₀ : List w8)
    (sr : Loc) (r : GoInterfaceOk) (off n : w64) (P : IProp GF) (Hd : Nat → w8 → Prop),
  io.writerPlain w → 0 ≤ sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ backend.writerOk w Wr ∗ Wr c bs₀ ∗
      io.secReader sr r off n ∗ io.readerAtOk r P Hd ∗ P }}
    (App (App (App (Val (@! _root_.Perennial.io.CopyN)) (Val #(GoInterface.ok w)))
      (Val #(interface.mkOk (go.GoType.PointerType _root_.Perennial.io.SectionReader.ty) #sr)))
      (Val #n))
  {{ (written : w64) (err : GoInterface), RET (PairV #written #err);
      ∃ (c' : Bool) (bs : List w8), P ∗ Wr c' (bs₀ ++ bs) ∗
        ⌜sint.Z written = bs.length ∧ bs.length ≤ n.toNat ∧
          (∀ j x, bs[j]? = some x → Hd (off.toNat + j) x) ∧
          (err = GoInterface.nil ↔ bs.length = n.toNat) ∧
          (c' = true ∨ (c' = c ∧ bs = []))⌝ }}

end spec

end EtcdGrove
end Perennial
