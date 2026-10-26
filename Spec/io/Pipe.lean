/-
`io.Pipe()` (names only in Perennial; D22 S-h, 2026-10-20): a synchronous in-memory pipe, its
reader end and its writer end. The trust boundary (an axiom in `Proof/io/Pipe.lean`), stated over
the pipe's writer predicate (`io.pipeW`, `Proof/io/Defs.lean`) and the backend's stream predicates
(`backend.writerOk`, `backend.readerStreams`: `Proof/go_etcd_io/etcd/server/v3/storage/backend/
InvSnapshot.lean`), the only use the verified code makes of a pipe (`newSnapshotReaderCloser`'s,
streaming a database snapshot to the transport).
-/
module

public import Proof.io.Defs
public import Perennial.Code.io

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

/-- `io.Pipe()`, for any promise `Φ` on the reader's complete streams and any hand-over `T`: the
reader `pr` (as an `io.ReadCloser`, read by one reader whose complete streams satisfy `Φ`:
`readerStreams`, given for `T`) and the writer `pw`, with the writer's contract (`writerOk` over
`pipeW pw Φ T`) at no bytes written and no `Write` returned. -/
abbrev io.Pipe.spec : Prop :=
  ∀ (Φ : List w8 → Prop) (T : IProp GF),
  {{ (True : IProp GF) }}
    (App (Val (@! _root_.Perennial.io.Pipe)) (Val #()))
  {{ (pr pw : Loc), RET (PairV #pr #pw);
      backend.writerOk ⟨go.GoType.PointerType _root_.Perennial.io.PipeWriter.ty, #pw⟩
        (io.pipeW pw Φ T) ∗
      io.pipeW pw Φ T false [] ∗
      (T -∗ backend.readerStreams
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.io.PipeReader.ty) #pr) Φ) }}

end spec

end EtcdGrove
end Perennial
