/-
Trust boundary: `io.PipeWriter.CloseWithError` (an axiom; see
`Spec/io/PipeWriter__CloseWithError.lean`). D22 S-h, 2026-10-20; `notes/decisions.md`, "D22 S-h
carried out".
-/
module

public import Spec.io.PipeWriter__CloseWithError

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

/-- **Trust boundary** (D22 S-h): `(*PipeWriter).CloseWithError(err)` is `w.pw.closeWrite(err)`
(`io/pipe.go`), which records `err` (`io.EOF` if nil) as the reader's error once, closes the
pipe's `done` channel and returns nil: the reader's later reads return that error after the bytes
already written, so its complete stream is the bytes written, of which the closer promised `Φ`
when `err` is nil, and, once a `Write` has returned, the hand-over `T`, which the reader's holder
gave up before its first read or close (see `Proof/io/Pipe.lean`). What would discharge it: the pipe's model of
`Proof/io/Pipe.lean`'s docstring. -/
axiom io.PipeWriter.CloseWithError.wp_proof :
  io.PipeWriter.CloseWithError.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
