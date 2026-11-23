/-
The specs `ioReadAtLeastPre.spec`, `ioReadFullPre.spec` of the local workaround in
`replica/IoReadFull.lean` (proved there; a defs module, so that `replica/ServeConn.lean` takes
`ioReadFullPre.spec` as a hypothesis, `EpReplicaDeps`, and `replica/Link.lean` passes the proof:
CLAUDE.md, "Import tiers").

**A local workaround of a Perennial gap** (`notes/perennial-changes.md`, 2026-11-23, "ReadAtLeast's
premise"): Perennial `7b2259a12`'s `io.ReadAtLeast`/`io.ReadFull` specs ask `Pre` of an empty read
(`len(ys) = len(buf)`), which a connection's reader contract (`net.conn_readerOk`, `0 < m`) refuses
(review C1 on #24). These are the specs of the branch `perennial-readatleast-prefix`
(`af905abba`, on `7b2259a12`: `Pre` only of the reads made, `len(ys) < min`), copied verbatim
but for their names (`ioReadAtLeastPre`, `ioReadFullPre`), over the same translated `io` code.
Drop this file for Perennial's once the pin has the change.
-/
module

public import Perennial.Proof.io.Reader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- `io.ReadAtLeast(r, buf, min)` of a reader `r` keeping the contract `Pre`, `S`, `E`
(`io.readerOk`), from `S r0`: delivers `ys` into the front of `buf` and leaves `S (r0 ++ ys)`,
returning `len(ys)` and an error as `io.readAtLeastRes` says (`eof`, `ueof`, `sb`: the values of
`io.EOF`, `io.ErrUnexpectedEOF`, `io.ErrShortBuffer`). Each `Read` is of `buf`'s remaining bytes,
after `ys` with `len(ys) < min` and `len(ys) < len(buf)` (the loop reads only while `n < min`, and
only once `min ≤ len(buf)`: else it returns `ErrShortBuffer` at once), so `Pre` must hold of every
such call, never of an empty read (a reader whose condition refuses `len(p) = 0`, a connection's,
qualifies). It may not return (a reader that keeps returning `0, nil`:
partial correctness). -/
abbrev ioReadAtLeastPre.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (min : w64) (eof ueof sb : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.readerOk ri Pre S E ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr io.ErrShortBuffer ↦□ sb ∗
      ⌜∀ ys : List w8, (ys.length : Int) < sint.Z min ∧ ys.length < xs.length →
        Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (App (Val (@! io.ReadAtLeast)) (Val #(interface.ok ri))) (Val #p)) (Val #min))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        io.readAtLeastRes E eof ueof sb r0 ys xs.length (sint.Z min) err }}

/-- `io.ReadFull(r, buf)` of a reader `r` keeping the contract `Pre`, `S`, `E`
(`io.readerOk`), from `S r0`: delivers `ys` into the front of `buf` and leaves `S (r0 ++ ys)`,
returning `len(ys)` and an error as `io.readFullRes` says (`nil` when all came; else the
reader's last error with its evidence, or `io.ErrUnexpectedEOF` for an `io.EOF` after some
bytes; `eof`, `ueof`: the values of `io.EOF`, `io.ErrUnexpectedEOF`). Each `Read` is of `buf`'s
remaining bytes, never empty (the loop reads only while some are left), so `Pre` must hold of every
such call. It may not return (a reader that keeps
returning `0, nil`: partial correctness). -/
abbrev ioReadFullPre.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (eof ueof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.readerOk ri Pre S E ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      ⌜∀ ys : List w8, ys.length < xs.length → Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (Val (@! io.ReadFull)) (Val #(interface.ok ri))) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        io.readFullRes E eof ueof r0 ys xs.length err }}

end spec

end Perennial
