-- The copy for the part `RaftNoAx/` of `Spec/google_golang_org/protobuf/proto/MarshalBootConfChange.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`proto.Marshal` of the `*raftpb.ConfChange` raft's `Bootstrap` builds (`bootstrap.go`:
`&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(peer.ID), Context: peer.Context}`): the
trust boundary (premises to axioms, item B, 2026-11-24). Until then the closed theorems took it as the
Iris premise `bootMarshal` (`Proof/go_etcd_io/raft/v3/ApiVocab.lean`), one per bootstrap log; now
`bootMarshal_of_spec` (`Proof/go_etcd_io/raft/v3/BootMarshal.lean`) derives it from this spec and the
bootstrap log's bytes (`bootWire`). Lean-first.
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.google_golang_org.protobuf.proto.BootWire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `proto.Marshal(cc)` of a `*pb.ConfChange` as raft's `Bootstrap` builds it (`bootConfChange p dq m`:
`Type` set to `m.type`, here `AddNode` (`0`), `NodeId` set to `m.nodeId`, `Id` unset (`nil`), `Context`
the slice holding `m.context`, `nil` when it is empty, no unknown fields), at any fraction, returns a
fresh slice holding exactly `ccBootWire m.nodeId m.context` and a `nil` error, and gives the message
back.

Why it is true of protobuf-go v1.36.12 (`proto/encode.go`, `internal/impl/codec_message.go`): `Marshal`
fails only on a required field unset, invalid UTF-8 in a validated string field, or a size mismatch
from a concurrent mutation; `raft.proto` is proto2 with no `required` and no `string` field, and the
caller's fraction excludes a concurrent writer, so the error is `nil`. The fast path encodes the
populated fields ordered by field number (`orderedCoderFields`), each as its tag and value with minimal
varints (`protowire.AppendVarint`), then the unknown fields (none here, `pbMsg … []`): an unset
optional field (`Id`, a `nil` `*uint64`; `Context`, a `nil` `[]byte`) is not written, a set one is,
even when it is `0` (proto2 explicit presence). So the bytes are `type` (`0x10 0x00`), `node_id`
(`0x18` and its varint) and, for a non-empty context, `context` (`0x22`, its length, its bytes): what
`ccBootWire` states. Go: `examples/premisefix/confchange`, `TestBootWireVectors` (the bytes, against
this formula, for ids from `0` to `2^64 - 1` and contexts absent, of 1, 81 and 300 bytes) and
`TestBootBytesDependOnPresence` (an `Id` set to `0`, a `Type` unset, an unknown field or an empty
non-`nil` context give other bytes: what `bootConfChange` excludes). The message is untouched but for
its size cache (hidden in `pbMsg`). -/
abbrev proto.MarshalBootConfChange.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : ConfChangeM),
  m.type = W32 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ bootConfChange p dq m }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p)))
  {{ (d : GoSlice), RET (PairV #d #interface.nil);
      bootConfChange p dq m ∗ d ↦* ccBootWire m.nodeId m.context }}

end spec

end EtcdGrove
end Perennial
