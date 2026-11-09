/-
`proto.Unmarshal(b, m)` (protobuf-go, assumed: `proto/decode.go`).

Users: grpc's codec on every receive (through `Grpc`'s specs), etcd's apply
(`pbutil.MustUnmarshal` of an `InternalRaftRequest`, 2d), raft's conf-change decoding (`doc.go`
pattern, 2d's `applyConfChange`), the WAL and snapshotter on restart (2e), rafthttp (2f).

Why true: `Unmarshal` resets the message (`*m = T{}`: only the top struct is written, never the
old submessages or slices, which `msgAt (own 1)` may hold read-only) and decodes into fresh
allocations, copying every `bytes` field (the default `UnmarshalOptions`, no aliasing); a malformed input or one nested beyond `RecursionLimit`
(`10000`) is an error, never a panic. A content that `encodes` the bytes and nests less than that
decodes, to that content (decoding is a function, `encodes_fun`).

Changes: from `specs-ref/.../proto/{Unmarshal,UnmarshalPb,UnmarshalConfChange*,UnmarshalUser,
UnmarshalRole}.lean`: one spec over `msgAt` and `encodes`.

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
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗ ∃ c, msgAt t p (DFrac.own 1) c ∗
      ((⌜err = GoInterface.nil ∧ encodes t c bs⌝ ∗ decodedAt t p) ∨
       ⌜err ≠ GoInterface.nil ∧ ∀ c', encodes t c' bs → ¬ depth c' < depthMax⌝) }}

end spec

end Proto
end EtcdGrove
end Perennial
