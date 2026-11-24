/-
**The bytes of a boot conf change** (premises to axioms, 2026-11-24): what protobuf-go's `proto.Marshal`
writes for the `*raftpb.ConfChange` raft's `Bootstrap` builds, `ConfChange{Type: AddNode, NodeId: id,
Context: ctx}` (`Id` unset, no unknown fields). Pure; the axiom that ties `proto.Marshal` to it is
`proto.MarshalBootConfChange.wp_proof` (`Spec/google_golang_org/protobuf/proto/MarshalBootConfChange.lean`).
-/
module

public import Proof.google_golang_org.protobuf.proto.UfWire

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove

/-- **`proto.Marshal` of `ConfChange{Type: AddNode, NodeId: id, Context: ctx}`** (`Id` unset, no
unknown fields; an empty `ctx` the absent field, a `nil` `Context`): the populated fields in field-number
order (`raft.proto`: `id = 1`, `type = 2`, `node_id = 3`, `context = 4`; `id` unset is not written), each
a tag and a minimal varint, `context` length-delimited: `type` (tag `0x10`) the varint `0` (`AddNode`),
`node_id` (tag `0x18`) the varint `id`, and, for a non-empty context, `context` (tag `0x22`) its length
and bytes. Checked against protobuf-go v1.36.12 (the examples module's pin) by
`examples/premisefix/confchange`, `TestBootWireVectors` (ids `0` to `2^64 - 1`, contexts absent, one
byte, a member's JSON, 300 bytes). -/
def ccBootWire (id : w64) (ctx : List w8) : List w8 :=
  [W8 0x10, W8 0x00, W8 0x18] ++ varintEnc (uint.nat id) ++
    (if ctx = [] then [] else [W8 0x22] ++ varintEnc ctx.length ++ ctx)

end EtcdGrove
end Perennial
