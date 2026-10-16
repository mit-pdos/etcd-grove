# etcd-io/raft#11: maxUncommittedLogSize not enforced across term changes

<https://github.com/etcd-io/raft/issues/11>. Open, filed 2022-12-21, label `bug`, raised in the
review of etcd-io/etcd#14627. No fix: no PR or commit, only proposals in the thread. Every
version is affected, including the raft pin `509271dac`.

**The bug.** `raft.reset` (`raft.go:781-809` at the pin) zeroes `r.uncommittedSize` at every
term change, `becomeLeader` included (`raft.go:938`). `increaseUncommittedSize`
(`raft.go:2090-2103`) checks that counter, not the uncommitted tail of the log. So a node
that leads again, with entries from its earlier terms still uncommitted, accepts another
`MaxUncommittedEntriesSize` worth. Over `k` terms the tail grows to `k ×` the limit, which
breaks `Config.MaxUncommittedEntriesSize`'s documentation (`raft.go:202-206`).

## Classification

**C-perf** (the spec is too weak: the resource bound is not stated). The decisive fact: the
specs abstract the size away. `NState` has no `uncommittedSize`, and
`raft.increaseUncommittedSize.spec` returns a bare `ok` that is constrained only for an
all-empty batch. `stepLeader` may drop a proposal at any time and puts no bound on what it
accepts. Every function on the path is verified, there is no premise about the limit, and the
behavior satisfies every spec. Reproduced at the pin (Go test, see Files). etcd's server does
not set the limit, so it runs with `noLimit` (`raft.go:313-315`).

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt`. All are "verified (sorry-free)".

| Go function | Spec |
|---|---|
| `raft.reset` (`raft.go:781`) | `Spec/go_etcd_io/raft/v3/raft__reset.lean`. Its model is `Defs.lean:1041` (`resetTo0`, `pci := 0`), with no size field |
| `raft.becomeLeader` (`raft.go:933`) | `raft__becomeLeader.lean` (model `becomeLeaderLog`, `Defs.lean:1102-1104`) |
| `raft.appendEntry` (`raft.go:812`) | `raft__appendEntry.lean` (has a drop path) |
| `raft.increaseUncommittedSize` (`raft.go:2090`) | `raft__increaseUncommittedSize.lean:64-75` |
| `raft.reduceUncommittedSize` (`raft.go:2108`) | `raft__reduceUncommittedSize.lean` |
| `stepLeader`, `MsgProp` | `stepLeader.lean:150-159` (`LeaderProposeResult`) |

## The argument (step 4)

1. **Observed.** At a leader of term `T`, the log has `(committed, last]` with
   `payloadsSize > MaxUncommittedEntriesSize + |one proposal|`. Each `MsgProp` accepted in term
   `T` returned `nil`.
2. **Premises.** `newRaft.spec` (`Spec/go_etcd_io/raft/v3/newRaft.lean:119-170`) takes
   `ConfigValid cv`, `CheckQuorum = false` and `DisableConfChangeValidation = false`, and
   nothing about `MaxUncommittedEntriesSize`. The reproduction meets all of them. No axiom
   is involved, since the size computation (`payloadsSize`) is verified.
3. **The postconditions allow it.** `raft.increaseUncommittedSize.spec` ends with
   `ownRaftPhysCV c c.voters r id s ∗ … ∗ ⌜(∀ e ∈ ents, e.Data' = []) → ok = true⌝`. The
   file's header says "the exact reject condition reads `r.uncommittedSize` and
   `r.maxUncommittedSize`, neither of which `NState` holds". `uncommittedSize` exists only as
   the raw field in `raftOwn` (`InvRaftPhys.lean:319`), with no invariant on it. So
   `appendEntry`'s `ok = true` with a growing tail meets the spec. `LeaderProposeResult`
   (`stepLeader.lean:150-159`) with `dropped = false` gives `proposed id {…}`, which appends
   whatever was proposed, so an accept is always consistent with the spec. The specs are
   partial correctness and say nothing about memory.
4. So the outcome satisfies every spec. The expected property, "the uncommitted tail stays
   within the limit", is not stated anywhere: **C-perf**.

## Proposal (step 6)

**`raft-uncommitted-bound`** (new). It is a safety stand-in for the resource bound, with
two layers.

- Add `ucs : Nat` to `NState` (or a conjunct of `ownRaftPhys` linking `rv.uncommittedSize'` to
  the log), plus a leader invariant
  `s.role = leader → payloadsSize (logSlice s.logst (s.logst.committed+1) (logLast s.logst+1)) ≤ ucs + inherited s`.
  Here `inherited` is the size of the tail at `becomeLeader`.
- `appendEntry`'s spec: `ok = true → ucs ≤ max ∨ batch empty`.

The documented property, `payloadsSize tail ≤ max + |last batch|`, then fails at the pin,
because `inherited` is unbounded (it is reset rather than carried over). It would be provable
after a fix that recomputes `uncommittedSize` from the tail at `becomeLeader` (one of the
issue's options). That needs a `raftLog.scan` spec over the unstable and stable parts. Cost:
small to medium (one new `NState` field threaded through `reset`, `becomeLeader`, `appendEntry`,
`reduceUncommittedSize` and `Step`'s `MsgStorageApplyResp` case, with no protocol-level change).
A real memory bound is outside partial correctness. The invariant above is the closest safety
property that this bug violates.

## Files

- `issues/raft-uncommitted-size-reset-across-terms.md` (new, `upstream: known`).
- `issues/raft-uncommitted-size-reset-across-terms/uncommitted_reset_test.go`. It fails at
  `509271dac`, with the tail at 640 bytes after 5 terms against a limit of 128.
