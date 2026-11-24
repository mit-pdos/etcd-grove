# `proto.UnmarshalWalRecordE.wp_proof` (2026-11-24, branch `wal-safe-review`)

**The axiom**: `Proof/google_golang_org/protobuf/proto/UnmarshalWalRecordE.lean`,
`axiom proto.UnmarshalWalRecordE.wp_proof : proto.UnmarshalWalRecordE.spec`. Its statement is
`Spec/google_golang_org/protobuf/proto/UnmarshalWalRecordE.lean`'s spec, **verbatim and unchanged**: the
spec that was `etcd_wal_safe`'s premise `Hopen : ∀ hG, TOpen …` (`TOpen`'s only field,
`unmarshalWalRecordE`), and before that a hypothesis of the WAL's and the tester's Links
(`h_proto_UnmarshalWalRecordE`). Nothing moved into the trust base that the theorem did not already rest
on; it moved from the statement (a hidden Hoare triple, which the robustness bar forbids: #49's etcd
report, item 5) into a per-function axiom at the trust boundary, where the trust-base tools see it.

**Why it holds in Go**: the spec file's header (protobuf-go v1.36: `Unmarshal` of a byte slice fails
with `internal/errors`' errors, `protowire.ParseError`'s or `errors.RequiredNotSet`, none `io.EOF` or
wrapping it; their `Is` methods compare and their `Unwrap` chains are finite).

**Interim**: retired by etcd-grove#37 S3, which extends `proto.UnmarshalPb.spec` with the error's
identity and proves this spec from it.

**Not reviewed** by the `axiom` skill: no attack run. The success half is `proto.UnmarshalWalRecord.spec`'s
(proved from `proto.UnmarshalPb.wp_proof`); the failure half adds `errIsNot err t ∗ errIsTerm err`.
