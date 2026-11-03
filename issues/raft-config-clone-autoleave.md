---
upstream: none
checked: 2026-11-01
links:
blocks-proof: no
---

# raft: `Status()` reports `AutoLeave: false` in a joint configuration entered with auto-leave

In a joint configuration entered with auto-leave (a `ConfChangeV2` with the `Auto` or
`JointImplicit` transition), `Status().Config.AutoLeave` is false and `Status().Config.String()`
omits "autoleave", although the node's configuration has it and will leave the joint state on its
own. `ApplyConfChange`'s `ConfState` reports it correctly.

**Expected:** `Status().Config` should be a copy of the configuration, `AutoLeave` included, as
[`Config.Clone`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tracker/tracker.go#L95-L112),
which `Status` uses, documents: "a copy of the Config that shares no memory with the original".

**Impact:** an application that reads `Status().Config.AutoLeave` to decide whether it must propose
leaving a joint configuration itself gets the wrong answer (a redundant leave proposal, which the
leader refuses), and logs or debug output of the status omit "autoleave". Nothing inside raft
reads the cloned field. etcd never enters a joint configuration and is not affected. Same code in
v3.7.0.

**Reproduction:** `TestRawNodeStatusAutoLeave` in
[`issues/raft-config-clone-autoleave/status_autoleave_test.go`](raft-config-clone-autoleave/status_autoleave_test.go)
(a single-voter `RawNode` leader applies a `ConfChangeV2` with `JointImplicit` adding voter 2,
which never answers, so the configuration stays joint), copied into the module root at
etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/amd64:

```
$ go test . -run '^TestRawNodeStatusAutoLeave$' -count=1
raft2026/11/01 04:11:00 INFO: 1 switched to configuration voters=(1 2)&&(1) autoleave
--- FAIL: TestRawNodeStatusAutoLeave (0.00s)
    status_autoleave_test.go:72:
        	Error:      	Should be true
        	Messages:   	Status().Config: voters=(1 2)&&(1)
FAIL
```

**Cause:** `Clone`'s result literal lists only the voter and learner sets, so `AutoLeave` takes
its zero value; [`getStatus`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/status.go#L74)
reports the configuration through `Clone`.

## Proof

no: `tracker.Config.Clone.spec` states the clone with `autoLeave := false`, as the code does
(`Spec/go_etcd_io/raft/v3/tracker/Config__Clone.lean`), and `confchange` overwrites the field
wherever it matters; no premise.

## Fix

Add `AutoLeave: c.AutoLeave` to `Clone`'s result literal.
