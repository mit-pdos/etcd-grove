/-
**The fields of a merged snapshot message** (`snap.Message`; rafthttp stage 7b, D42, 2026-10-24,
statement for review, **D22's interface**: to be agreed with the D22 owner). The snapshot sender
(`snapshotSender.send`, `createSnapBody`) reads `merged.Message`, `merged.TotalSize` and
`merged.ReadCloser`; `msgIs m ml rc` (`Proof/.../snap/Defs.lean`) is opaque, so this states what
those reads give: the raft message `ml`, some size, not negative (`proto.Size(ml) + rcSize`, the
snapshot's size; the sender adds it to a counter, whose `Add` panics on a negative), and the
exact-size reader `NewMessage` wrapped
around `rc` (`pioutil.NewExactReadCloser(rc, size)`), whose complete streams are `rc`'s (it returns
`io.EOF` only with `rc`'s, every byte passed through; on a short or long stream an error) and
whose `Close` (closing `rc`, the pipe's reader end: from any goroutine, concurrently with a `Read`,
more than once) returns. (Alternatively `msgIs` could be defined with these facts.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What reading a merged message's fields gives (see the file header). -/
abbrev snap.Message.fields.spec : Prop :=
  ∀ (m ml : Loc) (rc : GoInterface),
  msgIs (GF := GF) m ml rc ⊢
    structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message
      go!"Message" m ↦□ ml ∗
    (∃ tsz : w64, structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message
      go!"TotalSize" m ↦□ tsz ∗ ⌜0 ≤ sint.Z tsz⌝) ∗
    ∃ (rd : GoInterface) (ri : GoInterfaceOk),
      structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message
        go!"ReadCloser" m ↦□ rd ∗ ⌜rd = GoInterface.ok ri⌝ ∗
      □ (∀ Φ : List w8 → Prop, backend.readerStreams rc Φ -∗ backend.readerStreams rd Φ) ∗
      □ {{ (True : IProp GF) }}
          (App (Val #(methods ri.ty go!"Close" ri.v)) (Val #()))
        {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
