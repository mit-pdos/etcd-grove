// Package pbwire is the differential test of the candidate Lean wire semantics of protobuf
// (Proof/google_golang_org/protobuf/proto/PbWire.lean, which nothing trusts yet: protobuf stage 0',
// mit-pdos/etcd-grove#20). vectors_test.go builds messages of the types below with
// protobuf-go's reflection API on the real generated structs, marshals them with the real
// proto.Marshal (and, for the types in pbgen's subset, with the pbgen codec of protobuf.toml,
// which must agree byte for byte), unmarshals encodings and their mutations with the real
// proto.Unmarshal, and writes every input and outcome, with the types' descriptors from
// models.lab/pbdesc (the one descriptor source), as the Lean module
// Proof/google_golang_org/protobuf/proto/PbWireVectors.lean, whose #guards check the Lean
// semantics against them at every build. The test fails if that module is not what it writes
// (PBWIRE_UPDATE=1 rewrites it):
//
//	cd examples && GOWORK=off go test ./pbwire/
//	cd examples && PBWIRE_UPDATE=1 GOWORK=off go test ./pbwire/   # then lake build the module
//
// Types: raft's raftpb (proto2: explicit presence, unpacked repeated, closed enums), the WAL's
// walpb, etcd's etcdserverpb (proto3, oneofs: RequestOp, ResponseOp, Compare, WatchRequest),
// mvccpb, authpb, leasepb, and xpb (a copy of models/internal/pbdifftest/xpb: every scalar kind,
// packed repeated, recursion).
package pbwire
