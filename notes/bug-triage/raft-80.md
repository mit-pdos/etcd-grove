# etcd-io/raft#80: Configuration change validation has false positives

<https://github.com/etcd-io/raft/issues/80>. Open, filed 2023-07-10 by tbg, no labels. Related
PR etcd-io/raft#81 added `Config.DisableConfChangeValidation`; it is present at the raft pin
`509271dac` (`raft.go:1339`). There is no fix for the false positives. The thread proposes
tracking the configuration explicitly.

**The report.** `stepLeader`'s `MsgProp` case (`raft.go:1325-1345` at the pin) refuses a conf
change when `r.pendingConfIndex > r.raftLog.applied`. `becomeLeader` sets `pendingConfIndex` to
the last index of the log (`raft.go:953-957`, "Conservatively ..."), so a new leader refuses
every conf change until its whole log is applied, even when that log has no conf change. A
refused change becomes an empty normal entry. The issue calls these false positives: changes
refused that would be safe. It claims there are no false negatives.

## Classification

**N** (documented, conservative behavior; really a design request). Secondary **C-err**. The
decisive fact: `Node.ProposeConfChange`'s comment (`node.go:141-145`) says "configuration changes
are dropped unless the leader has certainty that there is no prior unapplied configuration
change in its log". The proved model states the refusal condition exactly:
`propConfStep` (`Proof/go_etcd_io/raft/v3/CCModel.lean:108-115`) refuses when
`applied < acc.pci ∨ ccWantsLeave c ≠ joint`, and `becomeLeaderLog` sets `pci := logLast s.logst`
(`Proof/go_etcd_io/raft/v3/Defs.lean:1102-1104`). `stepLeader`'s `LeaderProposeResult`
(`Spec/go_etcd_io/raft/v3/stepLeader.lean:150-159`) applies it. So the false positive is stated
by the spec, not hidden by it.

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt`. All are "verified (sorry-free)":
`stepLeader` (`raft.go:1275`, `Link.lean:1235`), `raft.becomeLeader` (`raft.go:933`), `raft.reset`,
`RawNode.ProposeConfChange` and `node.ProposeConfChange` (`Link.lean:1514`, `:1618`).

## The argument (step 4)

1. **Observed.** A leader just elected at term `T` with `applied < lastIndex` and no conf
   entry in `(applied, lastIndex]`. A `ProposeConfChange` is refused (appended as
   `zero_val EntryM`), and `nil` is returned.
2. **Premises.** `newRaft.spec` requires `DisableConfChangeValidation = false`
   (`Spec/go_etcd_io/raft/v3/newRaft.lean:135`), which is the default, so #81's option is out
   of scope. Nothing else bears on this.
3. **The postcondition gives exactly this outcome.** After `becomeLeader`, `s.pci = logLast`.
   With `applied < logLast`, `propConfStep` takes the refusing branch
   `(acc.1 ++ [zero_val EntryM], acc.2)`. Not X: the specs predict the report.
4. **The "no false negatives" claim.** Under the proofs' premise A1 (a `Ready`'s conf changes
   are applied before `Advance`, `DynCCPre`, `Spec/go_etcd_io/raft/v3/RawNode__ApplyConfChange.lean:101`),
   commit agreement under reconfiguration is proved (`raft_dyn_committed_agree`,
   `Protocol/ResultsDyn.lean:103`). So the guard has no unsafe false negatives there. Without A1
   it does. `Advance` before `ApplyConfChange`, which `doc.go` allows, lets the guard accept a
   second change while the first is not in use, and two entries can then be committed at
   one index. That is our finding `issues/raft-track-confchange-application.md`, which
   already links this issue. The thread's remedy ("precisely track and know the current
   and prospective config") is that file's fix.

## Proposal (step 6)

- **`confchange-validation-complete`** (new). The completeness half of the guard's spec: a
  conf change is refused only if there is an unapplied conf entry in `(applied, lastIndex]`, or
  `ccWantsLeave c ≠ joint`, where `joint` is the configuration after the log's last conf entry.
  In Lean: an invariant `s.role = leader → (applied < s.pci → ∃ i ∈ (applied, logLast], IsConfEnt (s.log i))`
  added to the leader's `ownRaftPhys` part. It fails at the pin because of `becomeLeader`'s
  `pci := logLast`. It would be provable with a `becomeLeader` that scans the uncommitted tail
  for the last conf entry (`hasUnappliedConfChanges`'s scan, already verified for `hup`), or
  with the explicit tracking of `raft-guards-track-applied-config`. Cost: small to medium (one
  invariant conjunct, the `becomeLeader` and `MsgStorageApplyResp`/`appliedTo` steps).
- The safety (false-negative) side is **`raft-guards-track-applied-config`** (existing). It drops A1.

## Files

None besides this report. Suggested `links:` line: `issues/raft-track-confchange-application.md`
already lists raft#80, so there is nothing to add.
