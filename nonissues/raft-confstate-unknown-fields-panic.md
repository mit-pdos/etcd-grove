---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/raft#168 pr open: related (draft since 2024-02, idle since 2025-02: witness support, adds ConfState fields 6 and 7; the only known proposal adding a ConfState field)
  - etcd-io/raft#133 issue open: related (the witness proposal #168 implements)
  - etcd-io/raft#423 pr merged: removed gogoproto.nullable from ConfState; not about unknown fields
  - etcd-io/raft#432 pr merged: passes ConfState as a pointer; not about unknown fields
blocks-proof: no
---
# raft v3.7: a snapshot whose `ConfState` has an unknown field panics the follower that restores it

A follower stepping a `MsgSnap` whose `ConfState` carries a field this version of `raftpb` does
not know panics ("ConfStates not equivalent after sorting"), and a node whose storage holds such a
`ConfState` panics in `newRaft` at every start. `ConfState.Equivalent` compares with `proto.Equal`,
which compares unknown fields, and the configuration raft rebuilds has none. A regression of the
move to protobuf-go v2 (v3.7): gogoproto's raftpb kept no unknown fields.

**Why not an issue:** not reachable as etcd uses raft: no raft version writes a field `ConfState`
does not have (none added since 2019; the only proposal, the witness draft etcd-io/raft#168, is
idle), so the test crafts the unknown field by hand; and raft dropped unknown-field forward
compatibility in 2021 (`3a3d196`). Revive it if a `ConfState` field is ever added.

`TestRestoreFromSnapMsgUnknownField` in
[`nonissues/raft-confstate-unknown-fields-panic/confstate_unknown_fields_test.go`](raft-confstate-unknown-fields-panic/confstate_unknown_fields_test.go)
(the fork branch's test, as a standalone file) fails at etcd-io/raft@c51f010c851e, go1.27.3:
`--- FAIL: TestRestoreFromSnapMsgUnknownField` / `panic: ConfStates not equivalent after sorting:`
(the two `ConfState`s differ only in `unknownFields:[]uint8{0x98, 0x6, 0x1}`).

## Proof

no: the conf state's ownership predicate requires no unknown fields (`csPts`,
`Proof/go_etcd_io/raft/v3/InvPb.lean`), and `ConfState.Equivalent.spec` is stated for such conf
states; etcd meets it, since no raft version writes one.

## Fix

**Branch**: `fix/raft-confstate-unknown-fields-panic` in `~/etcd-fixes/raft-confstate-unknown-fields-panic` (upamanyus/etcd-raft, pushed): b079b42 test, 71ca492 fix
**Base**: etcd-io/raft@638f42739b77572b5708eb0d8a776a272ade71ed

**PR draft**:

Title: raftpb: ignore unknown fields in ConfState.Equivalent

When raft restores a snapshot ([`restore`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1936)) or starts from its storage ([`newRaft`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L479)), it panics unless the snapshot's `ConfState` is [`Equivalent`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raftpb/confstate.go#L24-L52) to the configuration raft rebuilt from it, assuming, as `Equivalent`'s comment says, that it compares only the configurations its inputs describe. `Equivalent` compares the inputs with `proto.Equal`, which also compares unknown fields, and the rebuilt configuration has none. This PR makes `Equivalent` ignore unknown fields.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

A third commit (98c66a9) adds a `CHANGELOG-3.8.md` entry. The fix clears the clones' unknown
fields (`SetUnknown(nil)`), restoring the 2019 behaviour (`Equivalent` cleared
`XXX_unrecognized`); the alternative, comparing the four sorted slices and `AutoLeave` by hand,
would need updating for every new field.

## Notes

The 2026-10-23 review's Plan: "Nonissue, unless there's serious risk of a field being added and if
other types deal with unknown fields". The 2026-10-23 review (in git history) found neither:
`Equivalent` is raft's only message comparison outside tests, and etcd's WAL version check reads
only etcd's own protos.
