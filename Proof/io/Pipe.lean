/-
Trust boundary: `io.Pipe` (an axiom; see `Spec/io/Pipe.lean`). D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out".
-/
module

public import Spec.io.Pipe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (D22 S-h): Go's `io.Pipe` (`io/pipe.go`) returns the two ends of one
`pipe`, whose `Write` blocks until readers have consumed all of its bytes (or an end is closed:
then it returns how many were consumed and a non-nil error), so the bytes a reader gets are the
written bytes in order, and whose reader returns `io.EOF` only once the writer is closed with a nil
error (`CloseWithError(nil)`, as `Close`), any earlier error being returned instead: a complete
stream (every byte until `io.EOF`, no other error before) is all the bytes written before a nil
close, of which the closer promised `Φ` (`CloseWithError`'s spec). One reader holds
`readerStreams`, one writer `pipeW` (both exclusive), so the writes are serialized and nothing is
written after the close. The hand-over `T`: the reader's `readerStreams` exists only once `T` is
given up (the wand), and only its holder reads or closes the reader end (no other code has a
contract for it), while a `Write` returns only after a read of its bytes or a close of the reader
end (`pipe.write` sends on the unbuffered `wrCh`, or sees `done` or the reader's close): so a
writer whose `Write` has returned can take `T` (`CloseWithError`'s spec), which was given up
before. What would discharge it: a model of `io/pipe.go` (its mutex, its two
unbuffered channels and its `onceError`s) and a proof of `Write`, `Read` and `CloseWithError` over
it, with `readerStreams` and `pipeW` the halves of the stream's ghost state and `T` kept in it
from the reader's first operation to the writer's. -/
axiom io.Pipe.wp_proof : io.Pipe.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
