/-
**`*bufio.Reader` and `*bufio.Writer` over an `io.Reader` / `io.Writer` contract** (dsv-bufio,
2026-11-23, mit-pdos/etcd-grove#24): the vocabulary of `bufio`'s generic specs (`Spec/bufio/`:
`NewReaderSize`, `NewReaderOk`, `Reader__ReadOk`, `Reader__ReadByte`, `NewWriterSize`, `NewWriter`,
`Writer__Flush`, `Writer__Write`, `Writer__WriteByte`). Nothing here is about `net`: a connection's
instances of the contracts are laws of `Net/Proof/net/ConnIo.lean`. Ported from dsverify-lab's
`Harness/Proof/bufio/Defs.lean` (its `readerOk`/`writerOk` replaced by Perennial's `io.readerOk`
and `io.writerOk`, `Proof/io/WriterOk.lean`; its errors "with some message" by the contracts'
evidence).

**The buffered reader** `bufio.ownBufReader br ri Pre S E R`: `br` is a `*bufio.Reader` over the
reader `ri` (`io.readerOk ri Pre S E`, held); `R` is what it has returned so far; the underlying
stream has delivered `R ++ pend` (`S (R ++ pend)`, held by the reader), `pend` buffered; an error of
the underlying reader may be pending (returned once the buffered bytes are), with its evidence at
`R ++ pend` (`bufio.errE E`: `E`'s, or `io.ErrNoProgress`'s value, which `fill` returns after 100
empty reads). Every read the buffer makes of `ri` (at most its size, `bufio.preUpTo`) meets `Pre`.
So the bytes the reader returns are the stream's, in order, and its errors the stream's
(`Proof/bufio/ReaderLaws.lean`: a `*bufio.Reader` is itself an `io.readerOk` reader, so
Perennial's `io.ReadFull`/`io.ReadAtLeast` read through it).

**The buffered writer** `bufio.ownBufWriter bw wi J Q Ew sent pend err`: `bw` is a `*bufio.Writer`
over `wi` (`io.writerOk wi J Q Ew`, held); `sent` has gone to the underlying writer (`J sent`, held),
`pend` is buffered, not sent; `□ Q (sent ++ pend)` (what the buffer will send is allowed); `err` is
the writer's sticky error (`nil` while healthy, else with `Ew`'s evidence; once not `nil`, every
later `Write`, `WriteByte` and `Flush` returns it and sends nothing).
Lean-first.
-/
module

public import Proof.bufio.Base
public import Proof.bufio.PkgInit
public import Proof.io.WriterOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section pure

/-- Every read of `0 < m ≤ n` bytes, at any point of the stream, meets `Pre`. -/
def bufio.preUpTo (Pre : List w8 → Nat → Prop) (n : Nat) : Prop :=
  ∀ r m, 0 < m → m ≤ n → Pre r m

theorem bufio.preUpTo_trivial (n : Nat) : bufio.preUpTo (fun _ m => 0 < m) n :=
  fun _ _ h _ => h

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The evidence of a `*bufio.Reader`'s errors over a reader with the evidence `E`: `E`'s, or
the error is `io.ErrNoProgress`'s value. -/
def bufio.errE (E : List w8 → GoInterface → IProp GF) : List w8 → GoInterface → IProp GF :=
  fun r e => iprop(E r e ∨ globalAddr _root_.Perennial.io.ErrNoProgress ↦□ e)

/-- The fields of the `*bufio.Reader` `br` over `ri` buffering `pend` after returning `R`, with
the pending error `perr`: its buffer `buf` (`len(buf) > 0`, every read of at most its size meets
`Pre`) holding `pend` at `[r, w)`. -/
def bufio.readerRep (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (E : List w8 → GoInterface → IProp GF) (R pend : List w8) (perr : GoInterface) : IProp GF :=
  iprop(∃ (buf : GoSlice) (r w lb lrs : w64) (pre post : List w8),
    br ↦ _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) r w perr lb lrs ∗
    buf ↦* (pre ++ pend ++ post) ∗
    ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
      0 < (pre ++ pend ++ post).length ∧ bufio.preUpTo Pre (pre ++ pend ++ post).length ∧
      _root_.Perennial.io.ptrTyped perr⌝ ∗
    _root_.Perennial.io.errAt (bufio.errE E) (R ++ pend) perr)

/-- See the file header. -/
def bufio.ownBufReader (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) (R : List w8) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
    ∃ (pend : List w8) (perr : GoInterface), S (R ++ pend) ∗ bufio.readerRep br ri Pre E R pend perr)

/-- The fields of the `*bufio.Writer` `bw` over `wi` buffering `pend`, with the sticky error
`err`: its buffer `buf` (`len(buf) > 0`) holding `pend` at `[0, n)`. -/
def bufio.writerRep (bw : Loc) (wi : GoInterfaceOk) (Ew : GoInterface → IProp GF)
    (pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(∃ (buf : GoSlice) (n : w64) (rest : List w8),
    bw ↦ _root_.Perennial.bufio.Writer.mk err buf n (interface.ok wi) ∗ buf ↦* (pend ++ rest) ∗
    ⌜sint.Z n = pend.length ∧ 0 < (pend ++ rest).length⌝ ∗ io.werrAt Ew err)

/-- See the file header. -/
def bufio.ownBufWriter (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sent pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ io.writerOk wi J Q Ew ∗ J sent ∗
    □ Q (sent ++ pend) ∗ bufio.writerRep bw wi Ew pend err)

/-- A writer's sticky error has its evidence. -/
theorem bufio.ownBufWriter_err (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sent pend : List w8) (err : GoInterface) :
    bufio.ownBufWriter bw wi J Q Ew sent pend err ⊢ io.werrAt Ew err := by
  unfold bufio.ownBufWriter bufio.writerRep
  iintro ⟨-, -, -, -, %buf, %n, %rest, -, -, -, #H⟩
  iexact H

/-- A variable made by `errors.New` holds a pointer (`io.ptrTyped`). -/
theorem bufio.newVar_ptrTyped (X msg : GoString) (e : GoInterface) :
    _root_.Perennial.errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗
      ⌜_root_.Perennial.io.ptrTyped e⌝ := by
  iintro #Hv #He
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hx, -⟩
  icombine He Hx gives %Heq
  ipureintro
  subst Heq
  intro ii T h _
  cases h
  exact ⟨x, rfl⟩

end defs

end EtcdGrove
end Perennial
