---
upstream: none
checked: 2026-11-01
links:
blocks-proof: no
---
# raft: `MaxSizePerMsg: 0` panics on the first committed entry

A node configured with `MaxSizePerMsg: 0`, which `Config` documents as "at most one entry per
message", and `MaxCommittedSizePerReady` left unset panics in `Ready()` as soon as it has a
committed entry to apply ("applying entry size (0-0)=0 not positive"). `NewRawNode` and `StartNode`
accept the configuration; a bootstrapped node panics on its first `Ready`.

**Expected:** a configuration `Config.validate` accepts should run; with `MaxSizePerMsg` 0, as
[its documentation](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L189-L194)
says, the node should send (and apply) one entry at a time.

**Impact:** applications that set `MaxSizePerMsg` to 0 to get one entry per message and leave
`MaxCommittedSizePerReady` at its zero value: every node panics at startup, before any client
traffic. Easy to notice and to work around (set `MaxCommittedSizePerReady`), but the documented
value does not work. etcd is unaffected (it sets `MaxSizePerMsg` to 1 MiB). The code is the same in
v3.7.0.

**Reproduction:** `TestRawNodeZeroMaxSizePerMsg` in
[`issues/raft-zero-max-size-per-msg/zero_max_size_per_msg_test.go`](raft-zero-max-size-per-msg/zero_max_size_per_msg_test.go),
copied into the root package at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3:

```
$ go test . -run '^TestRawNodeZeroMaxSizePerMsg$' -count=1
raft2026/11/01 04:08:06 INFO: 1 switched to configuration voters=(1)
raft2026/11/01 04:08:06 applying entry size (0-0)=0 not positive
--- FAIL: TestRawNodeZeroMaxSizePerMsg (0.00s)
    zero_max_size_per_msg_test.go:64:
        	Error:      	func (assert.PanicTestFunc)(0x74d780) should not panic
        	            		Panic value:	applying entry size (0-0)=0 not positive
        	            	...
        	            	go.etcd.io/raft/v3.(*raftLog).nextCommittedEnts(0x1df29209ee60, 0x20?)
        	            		.../log.go:236 +0x17c
        	            	go.etcd.io/raft/v3.(*RawNode).readyWithoutAccept(0x1df2920b5140)
        	            		.../rawnode.go:144 +0xcf
        	            	go.etcd.io/raft/v3.(*RawNode).Ready(0x1df2920b5140)
FAIL
```

**Cause:** `validate` defaults `MaxCommittedSizePerReady` to `MaxSizePerMsg` when it is 0
([raft.go#L317-L321](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L317-L321)),
so both stay 0 and the log's apply budget is 0
([raft.go#L443](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L443)).
`nextCommittedEnts` treats an exhausted budget while applying is not paused as an invariant
violation and panics
([log.go#L234-L238](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/log.go#L234-L238));
applying pauses only once some entries are outstanding, so the first `Ready` with a committed
entry reaches the panic.

## Proof

no: `newRaft.spec` takes the premise `MaxCommittedSizePerReady ≠ 0 ∨ MaxSizePerMsg ≠ 0`
(`Spec/go_etcd_io/raft/v3/newRaft.lean`, carried by `NewRawNode`/`StartNode`/`RestartNode`), which
etcd meets (`MaxSizePerMsg` is 1 MiB).

## Fix

`validate` would default a zero `MaxCommittedSizePerReady` to a nonzero budget even when
`MaxSizePerMsg` is 0 (or `nextCommittedEnts` would hand out one entry when the budget is 0,
matching "at most one entry").

## Notes

INDEX-reviewed.md's Plan was "Nonissue, maybe docs" (a configuration precondition). Moved to
`issues/` under the new rule: the test uses only the public API with a value `Config` documents
as valid, and fails at `main`.
