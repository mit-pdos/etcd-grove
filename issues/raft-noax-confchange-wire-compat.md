---
upstream: none
checked: 2026-11-21
links: []
blocks-proof: no
---

# The noax Raft fork rejects a configuration change carrying an optional protobuf field

**Impact:** Adding an optional field to an otherwise identical configuration change causes
the public entry formatter to print an encoding error. The known change still
adds node 42. This affects both ConfChange and ConfChangeV2 on the noax fork
at `91e2ea70f48377487eccbf01bf80dd9787fac450`.

**Reproduction:** Copy the test to the root of that Raft revision and run
`go test . -run '^TestDescribeEntryWithNewConfChangeField$' -count=1`.
The test encodes each message with protobuf-go, adds an optional application
field through its reflection API, and compares the output of Raft's
`DescribeEntry` before and after. The VM reproduced the failure for both
message types. [Go test](raft-noax-confchange-wire-compat/confchange_wire_compat_test.go)

The V1 description changes from `0/0 EntryConfChange v42` to
`0/0 EntryConfChange raftpb: invalid conf change encoding`. The V2 description
changes in the same way.

**Expected:** Both descriptions still identify node 42.

**Cause:** The two decoders in `raftpb/noax.go` accept the exact field sequence produced
by the fork's encoder. Upstream uses protobuf-go, which accepts this extension.
The Raft fork uses those decoders in both the formatter and configuration-change
processing. [Fork source](https://github.com/upamanyus/etcd/blob/91e2ea70f48377487eccbf01bf80dd9787fac450/raftpb/noax.go)

## Proof

The noax kvdurable workload writes configuration entries using its own
encoder. Those entries use the field ordering and set that its decoder accepts.
The compatibility failure concerns other callers of Raft's public interface.
