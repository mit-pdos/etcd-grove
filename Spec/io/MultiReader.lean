/-
`io.MultiReader(buf, rc)` (names only in Perennial; rafthttp stage 7b, D42, 2026-10-24, statement
for review): the snapshot sender's body (`createSnapBody`), the envelope's buffer followed by the
merged message's reader. The trust boundary (an axiom once the sender's proof uses it, stage 7d),
stated over the buffer's bytes (`bufferM.ownBuffer`, `Proof/bytes/Buffer.lean`), the reader's
complete streams (`backend.readerStreams`, D22's: `Proof/go_etcd_io/etcd/server/v3/storage/backend/
InvSnapshot.lean`) and the HTTP boundary's stream contract (`http.streamHas`,
`Proof/net/http/Boundary.lean`). Go's `MultiReader` reads its readers in turn, each to its `EOF`,
and returns `EOF` only after the last one's: every prefix it yields is comparable with the
buffer's bytes `pre`, and a complete stream is `pre` followed by a complete stream of `rc`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.net.http.Boundary
public import Proof.bytes.Buffer
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `io.MultiReader(buf, rc)` of a buffer holding `pre` (as an `io.Reader`) and a reader of
complete streams in `Φ` (both taken): a reader of the stream `pre ++ t`, `t` a complete stream of
`rc`'s (see the file header). -/
abbrev io.MultiReader.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (b : Loc) (pre : List w8) (rc : GoInterface)
    (Φ : List w8 → Prop),
  {{ sl ↦*{dq} [interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #b, rc] ∗
      bufferM.ownBuffer (GF := GF) b pre ∗ backend.readerStreams rc Φ }}
    (App (Val (@! _root_.Perennial.io.MultiReader)) (Val #sl))
  {{ (mr : GoInterface), RET #mr;
      http.streamHas mr (fun x => x <+: pre ∨ pre <+: x) (fun x => ∃ t, x = pre ++ t ∧ Φ t) }}

end spec

end EtcdGrove
end Perennial
