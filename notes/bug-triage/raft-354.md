# etcd-io/raft#354: ConfChange silently converted to no-op without error notification

<https://github.com/etcd-io/raft/issues/354>. Open, filed 2025-11-30, no labels. The report is
against `main`. Two fix PRs, neither merged: etcd-io/raft#355 (closed) and etcd-io/raft#453 (open).
Both return an error from `Step` while still appending the no-op.

**The report.** At a leader, `stepLeader`'s `MsgProp` case (`raft.go:1325-1345` at the raft pin
`509271dac`) checks each conf-change entry of the batch. It refuses the entry if a conf change is
pending (`pendingConfIndex > applied`), if the entry is a non-leave change while the configuration
is joint, or if it is a leave request while the configuration is not joint. A refused entry is
replaced by `&pb.Entry{Type: EntryNormal}`. The batch is then appended and `Step` returns `nil`, so
the proposer (`RawNode.ProposeConfChange`, `node.ProposeConfChange`) cannot tell from the return
value that the change was refused. The report asks for an error. A maintainer (ahrtr) answers that a
`MsgProp` can batch several proposals, so a single error cannot describe a partial refusal. He adds
that etcd's request timeout bounds the wait. One commenter says etcd's `configure` waits forever. A
second commenter says the no-op entry sets a new pending boundary. That second claim is false: a
refused entry leaves `pendingConfIndex` where it was (code above; `propConfStep` below).

## Classification

**N** (not a bug: documented behavior, and the report is really a feature request). The decisive
fact: raft documents this behavior. `Node.ProposeConfChange`'s comment (`node.go:141-145` at the
pin) says: "the configuration change may be dropped with or without an error being returned. In
particular, configuration changes are dropped unless the leader has certainty that there is no prior
unapplied configuration change in its log". The proved spec of `stepLeader` also states exactly
this outcome. A refused conf-change entry becomes the empty normal entry, the batch is appended,
`dropped = false` (so `nil` is returned), and `pendingConfIndex` does not move
(`LeaderProposeResult` with `propConf`). The API-level spec `RawNode.ProposeConfChange.spec`
deliberately leaves out whether the change was appended or refused, and says so in its header.

Secondary, if upstream decides it is a bug: **C-err**. `ProposeConfChange`'s spec, like its
documentation, allows a `nil` return for a refused change. The precise outcome is known one level
down (`stepLeader`) and is not exposed at the API.

## The code path and its verification state

Source: the proof files directly. `verified.txt` was not yet written, and there is no
`.lake/tcb.json`. Every proof below is a `theorem` with no `sorry`, linked in
`Proof/go_etcd_io/raft/v3/Link.lean`.

| Go function | State | Spec |
|---|---|---|
| `node.ProposeConfChange` | verified (`Link.lean:1618`) | `Spec/go_etcd_io/raft/v3/node__ProposeConfChange.lean` ("whether the change is appended or refused is not visible", line 8) |
| `RawNode.ProposeConfChange` | verified (`Link.lean:1514`) | `Spec/go_etcd_io/raft/v3/RawNode__ProposeConfChange.lean` |
| `raft.Step` | verified (`Link.lean:1478`) | `Spec/go_etcd_io/raft/v3/raft__Step.lean` |
| `stepLeader` | verified (`Link.lean:1235`) | `Spec/go_etcd_io/raft/v3/stepLeader.lean` (`LeaderProposeResult`, :150) |
| `propConf` / `propConfStep` (pure model of the loop) | definitions | `Proof/go_etcd_io/raft/v3/CCModel.lean:108-119` |
| etcd `EtcdServer.configure` (the commenter's hang) | not verified (not in `etc/link-lean-first-server.txt`) | none |

## The argument (step 4)

1. **What the spec says the code does.** `LeaderProposeResult id s ents dropped s' joint`
   (`stepLeader.lean:150-159`), when `dropped = false`, gives a state `s'` that is
   `proposed id {s with pci := (leaderPropConf …).2} (leaderPropConf …).1` plus sends. Here
   `leaderPropConf` is `propConf` (`CCModel.lean:117`), and its step (`:108-115`) for a conf change
   `c` is:
   `if applied < acc.pci ∨ ccWantsLeave c ≠ joint then (acc.1 ++ [zero_val EntryM], acc.2) else
   (acc.1 ++ [x.1], li + |acc.1| + 1)`.
   So a refused change appends `zero_val EntryM` (an `EntryNormal` with no data) and keeps
   `pendingConfIndex`. The batch is appended (`proposed`), and the return is `nil` because
   `dropped = false`. This matches the reported behavior exactly. The spec also rules out the second
   commenter's claim: in the refused branch, `acc.2` is unchanged.
2. **Premises.** None of the premises bears on this. `Config.DisableConfChangeValidation = false`
   is `newRaft`'s premise (`stepLeader.lean` header), and that is the default. With validation
   disabled the check is skipped, and the report does not involve that case.
3. **At the API.** `RawNode__ProposeConfChange.lean`'s header: "Not stated: whether the change is
   appended or refused (a pending conf change, an empty `ConfChangeV2`), which `Step`'s
   postcondition does not expose and the error does not tell (a refused conf change is appended as
   an empty normal entry, `nil` returned)". So the spec allows exactly the outcome the reporter
   observed. That is intended: it matches `node.go`'s documented contract. It is not a gap that let
   an unintended behavior through.
4. **The etcd side.** At the etcd pin `107edf7e4`, `configure` (`server/etcdserver/server.go`)
   registers a waiter on `cc.Id` and selects on the waiter, `ctx.Done()` and `s.stopping`. A
   refused change is never applied as a conf change, so its waiter is never triggered, and the call
   returns when the request context's deadline expires (`parseProposeCtxErr`: `ErrTimeout`). It does
   not hang forever, except for a caller with no deadline, which etcd's gRPC handlers do not use.
   The client gets an error, though a misleading one (a timeout, not "refused"). This code is not
   verified here (O-fn if it were classified on its own). The comment (and the issue's
   `NotifyConfChangeApplied`) refers to some other code base, not etcd's `configure` at the pin.

No `issues/` file. The behavior is documented upstream, and the spec records it at both levels.

## Proposal (step 6; optional for class N)

**`confchange-propose-outcome`**: expose `stepLeader`'s accept/refuse outcome at the API, so that a
verified caller can tell a refused change from an accepted one (and so a change such as #453 would
show up as a spec change).

The sketch: `raft.Step.spec`'s `MsgProp` postcondition at a leader carries `LeaderProposeResult`'s
`cs` and `leaderPropConf` result, which `RawNode.ProposeConfChange.spec` restates as:
`err = nil → (¬leader) ∨ (∃ i, log' = log ++ [ccEntryM (some o) bs] ∧ pci' = i) ∨
(log' = log ++ [zero_val EntryM] ∧ pci' = pci ∧ (applied < pci ∨ ccWantsLeave o ≠ joint))`.

Cost: small to medium. The facts are already proved in `stepLeader`. The work is in threading them
through `raft.Step`'s model-witness postcondition and the `RawNode` and `node` specs: three spec
edits and their proofs, with no new invariant. It would not exclude this "bug". Only an API change
could, such as #453's returned error. The value is that the API spec would say precisely when a
change is refused, and that etcd's `configure` could then be specified. A guarantee that
`configure` returns, as opposed to waiting out its timeout, would be liveness, which is outside
partial correctness.
