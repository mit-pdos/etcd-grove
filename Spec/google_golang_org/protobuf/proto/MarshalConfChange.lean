/-
`proto.Marshal` of a raft v3.7 `*pb.ConfChange`: the trust boundary, stage R1. `MarshalConfChange`
encodes a conf change with it (`raftpb/confchange.go:48`), replacing gogoproto's generated
`ConfChange.Marshal` (the old axiom `raftpb.ConfChange.Marshal`).
Lean-first; stated over the raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`
(a raft v3.7 statement about `proto.*`, kept apart from the etcd side's `Clone.lean`, `Size.lean`,
`Marshal.lean`, `Unmarshal.lean`, as `MarshalIRR.lean` is from `Marshal.lean`; until stage R6 swapped
the raft trees, 2026-10-16, this file was the only one importing the `Raft37` tree's raftpb).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `proto.Marshal(cc)` of a `*pb.ConfChange` holding `m` (at any fraction) returns a fresh slice of
bytes that decode back to `m` (`ccDecodeV1`, what `proto.Unmarshal` makes of bytes, `CCModel.lean`) and
a `nil` error; the message is untouched but for its size cache (hidden).

Against protobuf-go v1.36.11 (`proto/encode.go`): `Marshal` fails only on a required field
unset, an invalid UTF-8 string (proto3 `string` or `enforce_utf8`) or a size mismatch from a
concurrent mutation; `raft.proto` is proto2 with no `required` and no `string` field, and the
caller's fraction excludes a concurrent writer, so the error is `nil`. The output is the
encoding of every populated field and the unknown fields, and `proto.Unmarshal` of it into a
`ConfChange` yields the same populated fields (proto2 presence: an unset scalar decodes unset and
reads as `0`, as `CCV1M` records it; `Context`'s bytes are the same, a `nil` and an empty one both
`[]`). No pure encoder is claimed (the bytes depend on which fields are set, which `CCV1M`
forgets): the round trip is the postcondition. -/
abbrev proto.MarshalConfChange.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : CCV1M),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ ownCCV1 p dq m }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p)))
  {{ (d : GoSlice) (bs : List w8), RET (PairV #d #interface.nil);
      ownCCV1 p dq m ∗ d ↦* bs ∗ ⌜ccDecodeV1 bs = some m⌝ }}

end spec

end EtcdGrove
end Perennial
