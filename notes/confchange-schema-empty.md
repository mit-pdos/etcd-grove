# `ConfChange`'s schema is `[]`: `MarshalConfChange[V2]`'s round trip at unconstrained unknown fields

Found 2026-11-12 by the out_size stage (C3, B2), recorded here by etcd-grove-81's decision. A gap
between a trust-boundary axiom's premise and what it is stated over, in this repository's specs (not
in the Go code): no verified program reaches it, and B2's option A1 closes it.

## What it is

`pbMsg T l uf` records `ufWire (pbSchemaOf T) uf`: the unknown fields `uf` are in the decoder-routed
form at the type's schema (a record of one of the message's own field numbers at its own wire type
is not left in `uf`, since the decoder routes it to the field). `pbSchemaOf` (`PbSchema.lean`)
gives `[]` for `raftpb.ConfChange`, `raftpb.ConfChangeSingle` and `raftpb.ConfChangeV2` ("no
registration models them"). At `[]` no field is known, so `ufWire [] uf` admits every `uf`: for
instance `uf = 08 05`, a varint record of field 1, which is `ConfChange.Id`.

`proto.MarshalConfChange.spec` (`Spec/google_golang_org/protobuf/proto/MarshalConfChange.lean`, an
axiom) claims `ccDecodeV1 (Marshal p) = some m` for every `ownConfChange p dq m`, and its docstring
says the unknown fields are constrained at the type's schema, "a record of the message's own field
number and wire type overrides that field". At schema `[]` they are not. In Go
(`examples/premisefix/confchange`, `TestRoundTripArbitraryUnknownFails`), a `ConfChange` whose
unknown fields hold such a record does not round-trip: decoding the encoding sets `Id` from the
unknown record, so the decoded message differs from `m`. The same holds of `ConfChangeV2`
(`MarshalConfChangeV2`, and each change's unknown fields).

## Why no verified program reaches it

An object with such unknown fields needs `ProtoReflect().SetUnknown` (not translated), or a struct
literal naming raftpb's unexported `unknownFields` (no raftpb code writes one). The objects the
verified code marshals are fresh literals (`pbMsg_alloc` at `uf = []`) or decoder outputs
(`proto.UnmarshalConfChange[V2]`, whose outputs are in the routed form). So there is no Go program
that uses the axioms, panics or returns a wrong result, and has a provable triple: it is a gap in
the axiom's stated premise, not a refutation.

## How it is closed

B2's option A1 (`/shared/tmp/out-size/freeze-b2.md` §2, approved by etcd-grove-81 pending its axiom
review): the three schemas go into `pbSchemaOf` (`ccSchema`, `ccsSchema`, `cc2Schema`, from
`raft.proto`), so `pbMsg` of the three types records the routed form, and `MarshalConfChange[V2]`'s
docstring becomes true with no change to their texts. The decoders' posts then claim the routed form
at the new schemas; Go evidence: `examples/pbschema/confchange_test.go` (`TestB2CCDecoderUf`).
