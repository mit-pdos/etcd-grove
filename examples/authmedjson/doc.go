// Package authmedjson is the evidence for the trust-boundary specs of `json.Marshal` on etcd's
// membership values (Spec/encoding/json/MarshalMember.lean, MarshalConfigChangeContext.lean;
// auth-mediation M2): run on etcd's `membership.Member` and `ConfigChangeContext` at the pin, at the
// pinned toolchain go1.27.3, each test panics or fails if a claim of the specs is false.
//
//   - never an error: TestNoError (invalid UTF-8, control bytes, escapes, extreme IDs, nil, empty and
//     filled slices, both types), TestFunctionOfFields (200k random values), TestNoErrorLarge and
//     TestHuge (hundreds of MB of output);
//   - a fresh result: TestFresh (no result overlaps another or an input, spare capacity included;
//     writes to one leave the others and the inputs unchanged);
//   - the inputs only read and borrowed: TestNoRetain (nothing retained), TestConcurrentReaders
//     (concurrent calls sharing the slices, under -race).
//
// The specs claim nothing about the bytes; TestFunctionOfFields also checks the output is a function of
// the fields (and of PeerURLs' nil-ness), which is not used.
//
// Run: GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./authmedjson/ (under a 32G memory cap); with
// GOEXPERIMENT=nojsonv2 etcd's server does not build at go1.27.3 (prometheus/common imports
// encoding/json/jsontext), so JSONv2's encoder is the only one etcd runs.
package authmedjson
