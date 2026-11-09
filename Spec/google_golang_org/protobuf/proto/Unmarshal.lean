/-
`proto.Unmarshal(b, m)` (protobuf-go, assumed: `proto/decode.go`).

Users: grpc's codec on every receive (through `Grpc`'s specs), etcd's apply
(`pbutil.MustUnmarshal` of an `InternalRaftRequest`, 2d), raft's conf-change decoding (`doc.go`
pattern, 2d's `applyConfChange`), the WAL and snapshotter on restart (2e), rafthttp (2f).

Why true: `Unmarshal` resets the message (`*m = T{}`: only the top struct is written, never the
old submessages or slices, which `msgAt (own 1)` may hold read-only) and decodes into fresh
allocations, copying every `bytes` field (the default `UnmarshalOptions`, no aliasing); a malformed input or one nested beyond `RecursionLimit`
(`10000`) is an error, never a panic. A content that `encodes` the bytes and nests less than that
decodes, to that content's wire view (decoding is a function up to `norm`, `encodes_fun`): an
unset field is left at its zero Go value, `nil` for a `bytes` or repeated field (proto3 never
encodes an empty one), so the decoded content is canonical (`norm c = c`).

Changes: from `specs-ref/.../proto/{Unmarshal,UnmarshalPb,UnmarshalConfChange*,UnmarshalUser,
Recheck (RR4): the success case states the decoded depth bound (`depth c < depthMax`: protobuf-go errors past `RecursionLimit`), the source of the stringers' depth premise for decoded requests (the apply's `irrMsgAt`).
UnmarshalRole}.lean`: one spec over `msgAt` and `encodes`.
verify-round (raft-conf-pb's request, A5-compl F4): on success the message is `mergeDst` (every
slice a fresh allocation owned to its capacity: `Unmarshal` resets and decodes into fresh
allocations; `mergeDst_msgAt` gives the old `msgAt (own 1)`).
verify-round (A6 F2): the persistent, address-keyed `decodedAt` replaced by the pure `norm c = c`
(the decoded content is canonical); a content-level fact cannot outlive a rewrite of the field.

Margin: on an error the message holds some partial content (the spec says some content).
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

/-- `proto.Unmarshal(b, m)` into an owned message: the content the bytes encode (always, if they
encode one that nests less than `depthMax`), or an error and some content. The bytes are read. -/
def Unmarshal.spec : Prop :=
  ∀ (t : go.GoType) (p : Loc) (c0 : Content) (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgAt t p (DFrac.own 1) c0 ∗ b ↦*{dq} bs }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #b)) (Val #(msgVal t p)))
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗ ∃ c,
      ((⌜err = GoInterface.nil ∧ encodes t c bs ∧ norm c = c ∧ depth c < depthMax⌝ ∗ mergeDst t p c) ∨
       (⌜err ≠ GoInterface.nil ∧ ∀ c', encodes t c' bs → ¬ depth c' < depthMax⌝ ∗
         msgAt t p (DFrac.own 1) c)) }}

end spec

end Proto
end EtcdGrove
end Perennial
