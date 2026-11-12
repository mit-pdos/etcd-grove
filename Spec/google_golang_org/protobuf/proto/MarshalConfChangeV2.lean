/-
`proto.Marshal` of a raft v3.7 `*pb.ConfChangeV2`: the trust boundary, stage R1. `MarshalConfChange`
encodes a conf change with it (`raftpb/confchange.go:52`), replacing gogoproto's generated
`ConfChangeV2.Marshal` (the old axiom `raftpb.ConfChangeV2.Marshal`).
Lean-first; stated over the raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`
(a raft v3.7 statement about `proto.*`, kept apart from the etcd side's `Clone.lean`, `Size.lean`,
`Marshal.lean`, `Unmarshal.lean`, as `MarshalIRR.lean` is from `Marshal.lean`; until stage R6 swapped
the raft trees, 2026-10-16, this file was the only one importing the `Raft37` tree's raftpb).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.raft.v3.PbContentOwn

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

/-- `proto.Marshal(cc)` of a `*pb.ConfChangeV2` holding `m` (at any fraction) returns a fresh slice of
bytes that decode back to `m` (`ccDecodeV2`, what `proto.Unmarshal` makes of bytes, `CCModel.lean`) and
a `nil` error; the message is untouched but for its size cache (hidden).

Against protobuf-go v1.36.12 (`proto/encode.go`): `Marshal` fails only on a required field
unset, an invalid UTF-8 string (proto3 `string` or `enforce_utf8`) or a size mismatch from a
concurrent mutation; `raft.proto` is proto2 with no `required` and no `string` field, and the
caller's fraction excludes a concurrent writer, so the error is `nil`. The output is the
encoding of every populated field and the unknown fields, and `proto.Unmarshal` of it into a
`ConfChangeV2` yields the same populated fields (proto2 presence: an unset scalar decodes unset and
reads as `0`, as `ConfChangeV2M` records it; `Context`'s bytes are the same, a `nil` and an empty one both
`[]`). No pure encoder is claimed (the bytes depend on which fields are set, which `ConfChangeV2M`
forgets): the round trip is the postcondition. (Premise fixes 1, 2026-11-10) The round trip
holds for the unknown fields an object of the verified programs can hold, which `pbMsg` now
constrains (`ufWire` at the type's schema, `PbSchema.lean`, per-type models stage A: unknown fields
as protobuf-go's decoder leaves them, which a re-decode puts back among the unknown fields), not for arbitrary bytes: a record of the message's own field number and
wire type overrides that field, and garbage does not decode (the premise attack; Go:
`examples/premisefix/confchange`, `TestRoundTripArbitraryUnknownFails` and
`TestRoundTripUnmarshalLeftovers`). Until then `pbMsg` admitted any bytes and this axiom was false
of `ProtoReflect().SetUnknown`'s objects (which no translated code makes).  (out_size B2, 2026-11-12: `notes/confchange-schema-empty.md`) The schemas were `[]` until then (the
message's and each change's), under which the claim above did not hold; they are now `cc2Schema` and
`ccsSchema` (`PbSchema.lean`).

**The length** (out_size B2, A3', 2026-11-12, decided by etcd-grove-81): `len(Marshal(cc))` is
`proto.Size`: at most `ccLenMax` (`PbContentOwn.lean`), every field counted present, an enum
sign-extended, each `ConfChangeSingle` a length-delimited field 2, each length's minimal varint;
the premise keeps every length below `2^63`. The precondition is the content form `ccPtsCC` (the
unknown fields of the message and of each change pinned). Go: `TestA3CC2Len` (gated). -/
abbrev proto.MarshalConfChangeV2.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (t : raftpb.ConfChangeTransition)
    (chs : List (ConfChangeSingleM × List w8)) (ctx uf : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      ccPtsCC (interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p) dq (.v2 t chs ctx uf) }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p)))
  {{ (d : GoSlice) (bs : List w8), RET (PairV #d #interface.nil);
      ccPtsCC (interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p) dq (.v2 t chs ctx uf) ∗
      d ↦* bs ∗
      ⌜ccDecodeV2 bs = some ⟨t, chs.map Prod.fst, ctx⟩ ∧
        (ccSize (.v2 t chs ctx uf) + 64 < 2 ^ 63 → bs.length ≤ ccLenMax (.v2 t chs ctx uf))⌝ }}

end spec

end EtcdGrove
end Perennial
