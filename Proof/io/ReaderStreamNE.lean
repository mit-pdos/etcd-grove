/-
**A stream reader that makes progress** (net/http's `ReadResponse`, 2026-11-23):
`io.readerStreamNE ri S E` is `io.readerStream ri S E` (`Proof/io/ReaderStream.lean`) whose `Read` of a
non-empty buffer delivers a byte or returns an error: never `(0, nil)`, which `io.Reader`'s contract
discourages ("Implementations of Read are discouraged from returning a zero byte count with a nil
error") and a TCP connection's `Read` never returns (the net extension's D1: `1 ≤ k` bytes for a
non-empty buffer). Over such a reader a `*bufio.Reader`'s `fill` reads once and never gives up with
`io.ErrNoProgress`, so `ReadByte` and `Peek` return only the stream's own errors
(`Spec/bufio/Reader__ReadByte.lean`, `Spec/bufio/Reader__Peek.lean`). Lean-first.
-/
module

public import Proof.io.ReaderStream

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

/-- See the file header. -/
def io.readerStreamNE (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (r : List w8) (p : GoSlice) (xs : List w8),
    {{ ⌜r.length + xs.length < 2 ^ 62⌝ ∗ S r ∗ p ↦* xs }}
      (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
            (xs ≠ [] → ys ≠ [] ∨ err ≠ GoInterface.nil)⌝ ∗
          io.errAt E (r ++ ys) err ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r ++ ys) }})

instance io.readerStreamNE_persistent (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : Persistent (io.readerStreamNE ri S E) := by
  unfold io.readerStreamNE; infer_instance

/-- A stream reader that makes progress is a stream reader. -/
theorem io.readerStreamNE_readerStream (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) :
    io.readerStreamNE ri S E ⊢ io.readerStream ri S E := by
  iintro #Hr
  iunfold io.readerStream
  iunfold io.readerStreamNE at Hr
  imodintro
  iintro %r %p %xs %Φ
  imodintro
  iintro Hpre HΦ
  iapply Hr $$ %r %p %xs [Hpre]
  · iexact Hpre
  inext
  iintro %n %err ⟨%ys, %hys, #He, Hp, HS⟩
  iapply HΦ
  iexists ys
  iframe Hp HS He
  ipureintro; exact ⟨hys.1, hys.2.1⟩

end defs

end EtcdGrove
end Perennial
