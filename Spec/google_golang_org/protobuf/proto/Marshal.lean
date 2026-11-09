/-
`proto.Marshal(m)` (protobuf-go, assumed: `proto/encode.go`).

Users: grpc's codec on every send (through `Grpc`'s specs, not directly), etcd's
`processInternalRaftRequestOnce` (`v3_server.go:1094`, 2c: an `InternalRaftRequest`), raft's
`bootstrap.go:56` (a `ConfChange`), raftpb's `MarshalConfChange` (3h), the WAL and snapshotter (2e).

Why true: `Marshal` computes the size, allocates it (`growcap`: the premise `encSize c < 2 ^ 48`
keeps `make` from panicking, `issues/grpc-codec-alloc-before-size-check.md`), and encodes field by
field, recursing per level (the depth premise); it fails (`errors`, no panic) exactly on an invalid
UTF-8 `string` field or an unset required field (`marshalOk`). The bytes are fresh.

Changes: round 1: deterministic output for a type without maps (`marshalOut`, 3h's request).
From `specs-ref/.../proto/{Marshal,MarshalPb,MarshalIRR,MarshalConfChange*}.lean`: one spec
over `msgAt`, the encoding a content-keyed relation (`encodes`), not `pbEnc ty l` of an address.
`MarshalIRR`'s depth premise (`notes/irr-depth.md`) is `fits`'s `depth c < depthMax`: what the
receiver's `Unmarshal` accepts.

Margin: the code also marshals deeper messages (up to the stack's limit), which then fail to
unmarshal.
-/
module

public import Spec.google_golang_org.protobuf.proto.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Proto

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- `proto.Marshal(m)` of a message holding `c` that fits: fresh bytes encoding `c`, or (an invalid
string, a required field unset) `nil` and an error. -/
def Marshal.spec : Prop :=
  ∀ (t : go.GoType) (p : Loc) (dq : DFrac) (c : Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgAt t p dq c ∗ ⌜c.fits⌝ }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal)) (Val #(msgVal t p)))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err); msgAt t p dq c ∗
      ((⌜err = GoInterface.nil ∧ marshalOk c⌝ ∗ ∃ bs : List w8, b ↦* bs ∗
          ⌜encodes t c bs ∧ (noMaps t → bs = marshalOut t c)⌝) ∨
       ⌜err ≠ GoInterface.nil ∧ ¬ marshalOk c⌝) }}

end spec

end Proto
end EtcdGrove
end Perennial
