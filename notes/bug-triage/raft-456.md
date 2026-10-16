# etcd-io/raft#456: TLA+ Raft model permits split-brain during membership changes (missing log guard)

<https://github.com/etcd-io/raft/issues/456>. Open, filed 2026-06-22. Two open PRs change the TLA+
model only: etcd-io/raft#458 ("fix TLA+ specification to match unapplied config guard") and #469
("tla: block campaigns with unapplied config changes"). Neither is merged, and the maintainers say
nobody can review TLA+.

**The report.** `tla/etcdraft.tla`'s `Timeout`/`RequestVote` do not model `hup`'s
`hasUnappliedConfChanges` guard (`raft.go:983` at the raft pin `509271dac`). The model therefore
lets a node campaign under a configuration two conf changes behind its committed log. Take
`{1,2,3}`, then `+4` and `+5`, both committed. `s2` has applied `+5` and `s3` has applied
neither. `s2` wins with `{2,4,5}` and `s3` with `{1,3}` in the same term. TLC finds
`MoreThanOneLeaderInv` violated. The reporter says the Go code is not affected.

## Classification

**N** (a bug in the TLA+ model, not in the Go code), with secondary **A-pre**. The Go code has
the guard, and this repository's model has it too: the dynamic model's `StepR.campaign`
requires `NoConfIn r.full applied commit` (`Proof/go_etcd_io/raft/v3/Protocol/StepR.lean:139`),
and the code-level spec of `hup` refines it. Under it, election safety at a changing
configuration is proved (`raft_dyn_election_safety`, `Protocol/ResultsDyn.lean:130`). The
secondary class: "the Go code is safe" holds only under A1, that is, `ApplyConfChange` before the
`Advance` that acknowledges the entry. The guard reads raft's `applied` index, not the
configuration in use. Raft's documentation allows `Advance` first, and then the Go code runs this
very trace: `issues/raft-advance-before-applyconfchange.md`, execution 2 "Follower lag", checked
in its abstract model (`issues/raft-conf-lag-model/trace-followerlag.txt`). Its leader-lag
variant is reproduced by a Go test at the public API (`leaderlag_test.go`).

## The code path and its verification state

Source: the spec, proof and `Link.lean` files directly (no `verified.txt`).

| Go function | State | Spec |
|---|---|---|
| `raft.hup` | verified | `Spec/go_etcd_io/raft/v3/raft__hup.lean:44` (`HupOkC`, with `HupGuard`) |
| `raft.hasUnappliedConfChanges` | verified | `Spec/go_etcd_io/raft/v3/raft__hasUnappliedConfChanges.lean:43` |
| `raft.Step` (dynamic mode: `StepR`) | verified | `Spec/go_etcd_io/raft/v3/raft__Step.lean`, premises `GMode.Pre` (`Proof/go_etcd_io/raft/v3/StepGhostMode.lean:57`) |
| `RawNode.ApplyConfChange`, `RawNode.Advance` | verified (dynamic mode) | `Spec/go_etcd_io/raft/v3/RawNode__ApplyConfChange.lean`, `RawNode__Advance.lean:78` |

## The argument

1. **The guard is the step that matters.** `notes/reconfiguration-safety.md` §0 and §4.1 say
   that the campaign guard is needed in exactly one place. It makes the candidate's
   configuration the fold of its whole committed prefix (I2). I1 then gives "at most one conf
   entry above commit" (any node, any `MsgApp` slice; `StepRInv.lean`, `ConfI1`). So a
   candidate's configuration is at most one conf change behind any log it can hold, and
   adjacent configurations overlap (`fold_adjacent`, `CfgOverlap.lean`). The TLA+ trace needs
   `s3` to campaign two changes behind. `StepR.campaign` forbids that: `+4` is in
   `(applied, commit]` of `s3`.
2. **What the reporter's step 4 needs in Go.** For `s3` to have `applied ≥ commit` while still on
   `{1,2,3}`, it must have `Advance`d past `+4` and `+5` without calling `ApplyConfChange`.
   `RawNode.Advance.spec`'s dynamic-mode premise excludes that:
   `NoConfIn rs.delivered rs.capplied rs.delivered.length` (`RawNode__Advance.lean:86`, "A1").
   `doc.go:94-103` and `node.go`'s `Advance` comment allow it ("may be done at any time after
   step 1"; "may call Advance while it is applying"). So the premise is real and undocumented,
   and that is our existing finding.
3. **The leader side** (the report's step 3, a second conf change proposed while the first is
   unapplied) is refused by `stepLeader`'s `alreadyPending` (`raft.go:1326`), which is the
   model's `propConf`. It has the same `applied`-based weakness under A1's violation
   (`issues/raft-advance-before-applyconfchange.md`, "Leader lag").

So the TLA+ model is weaker than the code and than our model. "The Go code is not affected"
holds for callers that meet A1, which the documentation does not require.

## Proposal

None new for the TLA+ model (class N). For the secondary A-pre, there are two existing
directions, both recorded in `issues/`. Document A1 upstream
(`issues/raft-document-confchange-before-advance.md`), or make the guards follow the
configuration in use (`issues/raft-track-confchange-application.md`, prototype
`guard-fix.patch`). Re-verifying with the guard fix would let `RawNode.Advance.spec` drop
A1. Slug: `raft-guards-track-applied-config` (medium: the `applied`-based guards in
`hup`/`stepLeader` and the `ApplyConfChange` bookkeeping, re-proved in the dynamic mode).

## Files

None written. Suggested link (the line already exists in
`issues/raft-advance-before-applyconfchange.md`; add it to
`issues/raft-track-confchange-application.md`):
`- etcd-io/raft#456 issue open: related, not this bug: the TLA+ model lacks the hasUnappliedConfChanges guard; its trace is the Go code's under Advance before ApplyConfChange`.
