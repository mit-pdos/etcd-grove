# Reproduction Tests for `etcd-io/etcd#22634`

This directory contains standalone Go reproduction tests (`repro_test.go`) exercising the code of `etcd-io/etcd#22634` (`etcdserver: replay legacy v2 metadata WAL entries`, commit `2e8c3386ff7db129d8d311eb00b47edcb0f10d8e`, applied to `/root/etcd-pr/etcd-22634` on branch `pr-etcd-22634-goose-lean`).

## Contents

- `repro_test.go`: Unit tests reproducing all three findings identified during formal verification of `etcd#22634`:
  1. `TestFinding1_UnanchoredMemberAttributePathRegexp`:
     - `1a_PrefixAndSuffixAcceptedAsMemberAttrSet`: Disallowed v2 `PUT` paths with a leading prefix (`"/prefix/0/members/1a2b/attributes"`) or trailing suffix (`"/0/members/1a2b/attributes_extra"`) match the unanchored `memberAttributePathRegexp` (`legacy_request.go:32`) and have `path.Base(path.Dir(r.Path)) == "1a2b"`, so `apply.Apply` silently converts them into `ClusterMemberAttrSetRequest{Member_ID: 0x1a2b, ...}` instead of panicking with `"detected disallowed v2 WAL for stage --v2-deprecation=write-only"`.
     - `1b_TrailingSegmentsParseWrongMemberID`: A disallowed v2 `PUT` path with two extra trailing segments whose parent segment is hexadecimal (`"/0/members/1a2b/attributes/deadbeef/subkey"`) matches `memberAttributePathRegexp` and causes `MustParseMemberIDFromKey(lg, path.Dir(r.Path))` to parse `"deadbeef"` (`0xdeadbeef`) instead of `"1a2b"` (`0x1a2b`) as the target `Member_ID`.
     - `1c_SingleTrailingSegmentPanicsInParseUint`: A disallowed v2 `PUT` path with one extra trailing segment (`"/0/members/1a2b/attributes/extra"`) matches `memberAttributePathRegexp` and panics inside `MustParseMemberIDFromKey` (`strconv.ParseUint: parsing "attributes": invalid syntax`) instead of the expected `"detected disallowed v2 WAL"` panic.
  2. `TestFinding2_ProtoUnmarshalWireOverlapBypass`:
     - `2a_LegacyRequestBytesWithEmptyPathAndVal`: Because field 2 of `etcdserverpb.InternalRaftRequest` is `reserved 2; reserved "v2";` (`raft_internal.proto:40`), `proto.Unmarshal(e.Data, &raftReq)` silently skips tag 2 (`Method`). When `legacyRequestBytes(42, "DELETE", "", "")` (the PR's own test helper in `apply_test.go`) encodes a disallowed v2 method with empty `Path` and `Val` (omitting `Dir`), `proto.Unmarshal` returns `err == nil` with `Range: &RangeRequest{}, Put: &PutRequest{}`, bypassing the `if err != nil` legacy fallback in `apply.Apply`.
     - `2b_InternalRaftRequestWrappingV2InField2`: An `InternalRaftRequest` wrapping a v2 request in field 2 (`V2`, handled in etcd 3.6 via `if raftReq.V2 != nil`) succeeds in `proto.Unmarshal` (`err == nil`), drops field 2 as an unknown field, and dispatches an empty `InternalRaftRequest` (`ClusterVersionSet == nil`).
  3. `TestFinding3_WALMinimalEtcdVersionPanicsOnLegacyV2Entries`:
     - Commit `073d46a558de734e5e86ff2f84cd2f54f990f75d` (`Remove the v2 Request message`) removed the v2 `Request` fallback in both `server/etcdserver/apply/apply.go` and `server/storage/wal/version.go` (`visitEntryData`). `etcd#22634` restores the fallback in `apply.go` but not in `wal/version.go`, so `wal.MinimalEtcdVersion` panics when given a WAL containing the very legacy v2 `/0/version` or `/0/members/<id>/attributes` entries that `etcd#22634` replays.
- `go.mod`, `go.sum`: Module definition pointing via `replace` to `/root/etcd-pr/etcd-22634`.
- `test.log`: Output of `go test -v ./...`.

## How to Run

```bash
cd /shared/etcd-grove-pr/etcd-22634/notes/pr-verify/etcd-22634
go test -v ./...
```
