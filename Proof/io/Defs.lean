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

end defs

end io
end EtcdGrove
end Perennial
