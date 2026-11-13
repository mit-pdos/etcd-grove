/-
**`io.Pipe`'s writer end** (names only in Perennial; D22 S-h, 2026-10-20; `notes/decisions.md`,
"D22 S-h carried out"): the vocabulary of the pipe's trust-boundary specs
(`Spec/io/Pipe.lean`, `Spec/io/PipeWriter__CloseWithError.lean`). Lean-first (no Rocq
counterpart).

* `pipeW pw Φ T c bs` (opaque, exclusive): the right to write to, and to close, the writer end `pw`
  of a pipe whose reader's complete streams are promised to satisfy `Φ`, the bytes `bs` written
  so far, `c` whether a `Write` has returned. It is the client predicate of the writer's contract
  (`backend.writerOk`, whose `Write` appends to `bs`); `CloseWithError(err)` takes it, with `Φ bs`
  if `err` is nil: the reader's complete stream is then `bs` (`io.Pipe` hands its bytes over
  unbuffered, in order, and its reader returns `io.EOF` only after the writer's close with a nil
  error). The reader's half is `backend.readerStreams` (`InvSnapshot.lean`).
* `T`, the pipe's **hand-over**: `io.Pipe` gives the reader's `readerStreams` only for `T` (a
  wand), and `CloseWithError` gives `T` back to the writer once a `Write` has returned (`c`):
  a pipe's `Write` returns only after its reader read or closed, which needs `readerStreams`. The
  sender passes its half of the backend snapshot this way (`T`: its share, after it read the
  snapshot's `Size`), so that the writer's goroutine closes the whole snapshot (`createMergedSnapshotMessage`,
  `newSnapshotReaderCloser`): the order Go gets from the pipe's blocking `Write`.
* `rcCloseOk r` (persistent; sweep repairs 1, S1): `r`'s `Close` returns. The pipe's reader has it
  with its `readerStreams`, for `T`; `snap.NewMessage` takes it of its reader.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace io

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer end `pw` of a pipe promised to `Φ` with the hand-over `T`, at the bytes `bs`
written, `c` whether a `Write` has returned** (opaque, exclusive; see the file header). -/
opaque pipeW (pw : Loc) (Φ : List w8 → Prop) (T : IProp GF) (c : Bool) (bs : List w8) :
  IProp GF

/-- **The `io.Closer` `r`'s `Close` returns** (persistent; sweep repairs 1, S1, 2026-11-08,
`notes/axiom-review/snap-stream.md`): `r` is a non-nil interface whose `Close()` returns (some
error), from any goroutine, any number of times, concurrently with a `Read`. `io.Pipe`'s reader
has it only with its `readerStreams`, once the pipe's hand-over `T` is given up (`Spec/io/Pipe.lean`):
closing the reader end lets the writer's `Write` return, which hands `T` to the writer. What
`snap.NewMessage` takes of its reader (the message's `CloseWithError` and its wrapper's `Close`
close it). -/
def rcCloseOk (r : GoInterface) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜r = GoInterface.ok ri⌝ ∗
    □ {{ (True : IProp GF) }} (App (Val #(methods ri.ty go!"Close" ri.v)) (Val #()))
      {{ (err : GoInterface), RET #err; True }})

instance rcCloseOk_persistent (r : GoInterface) : Persistent (rcCloseOk (GF := GF) r) := by
  unfold rcCloseOk; infer_instance

end defs

end io
end EtcdGrove
end Perennial
