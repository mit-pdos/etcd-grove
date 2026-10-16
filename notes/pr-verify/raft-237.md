# etcd-io/raft#237: breaking: Remove `RawNode.TickQuiesced()`

- PR: https://github.com/etcd-io/raft/pull/237, head `4a66f91bf8e47936cabe9cdf0a8b1fa64b81a385`
  (open, one commit, based on raft `d155efc81`; a maintainer said it will be merged once
  release-3.6 is cut).
- Fork commit: `d7b2b0826` on `pr-raft-237-goose-lean` (worktree `~/etcd-pr/raft-237`), the PR
  applied to the pinned `raft37-goose-lean` (`509271dac`). It applied cleanly (`git apply -3`, no
  conflicts, no rewrites), so the verified code is exactly what the PR does. `go build ./...` and
  `go test ./...` (raft, confchange, quorum, raftpb, rafttest, tracker) pass.
- Translation: `etc/goose.py --project raft --src raft=~/etcd-pr/raft-237`. The only changes to
  `Code/go_etcd_io/raft/v3.lean` are the removal of `RawNode.TickQuiesced.impl`, of its field
  `ptr_TickQuiesced_unfold` in `RawNode.TypeAssumptions`, and of that field in the instance list,
  plus shifted `go: rawnode.go:N` comments. `GeneratedProof/` is unchanged. The pin in
  `etc/goose.py` is left alone, so `etc/goose.py --check` fails on this branch, as expected.

## Verdict

The PR is sound. It removes a deprecated, unspecified method (`rn.raft.electionElapsed++`) that
nothing in raft or etcd calls. No spec or proof mentions it, and every proved result still builds
against the new translation (below). Removing a `MethodUnfold` field from
`RawNode.TypeAssumptions` only weakens a hypothesis of the specs, so the trust base shrinks by one
assumption about the code. The removal changes the API only. The removed method could not have
broken a safety invariant: the raft predicate does not constrain `electionElapsed`, and the
`Tick` proofs already cover every value of it. What needs a maintainer's decision is not
correctness but release management. The PR deletes an exported method from the
`go.etcd.io/raft/v3` module, while issue #66 had planned that for v4, and it adds no CHANGELOG
entry for the removal.

## Changed functions

| Function | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| `RawNode.TickQuiesced` (rawnode.go:78) | removed | translated, no spec (the only `RawNode` method without one) | gone | nothing to prove; callers checked (none) |

No types, struct fields or package-level variables change. The field `raft.electionElapsed`
stays, and is still written by `tickElection`, `tickHeartbeat`, `reset` and the vote handlers.

## Caller graph

- In Go, `TickQuiesced` appears nowhere in raft (`upstream/main`, the PR head, the fork) or in etcd
  (`upstream/main`, `origin/goose-lean`) apart from its definition and the deprecation entry in
  `CHANGELOG/CHANGELOG-3.6.md`. A search for `quiesce` finds no other use. It is not part of the
  `Node` interface, so no interface or method-value use exists.
- In Lean, no `Spec/`, `Proof/`, link file (`etc/link-lean-first-*.txt`), `notes/` or `issues/`
  file names it. No proof builds a `RawNode.TypeAssumptions` value.

So there are no callers to re-check.

## Why the removal is safety-neutral

The old method would have kept `ownRawNode γ rn id rs` with `rs` unchanged:

- `raftOwn`'s field for `electionElapsed` is a bare points-to
  (`Proof/go_etcd_io/raft/v3/InvRaftPhys.lean:321`).
- `raft.wp_store_electionElapsedC` (same file, around line 3070) stores any value and keeps the
  same abstract state `s`.
- The `int` addition wraps and cannot panic.

`tickElection` and `tickHeartbeat` read the counter as an arbitrary value
(`raft.wp_load_electionElapsedC`), so `RawNode.Tick.spec`
(`Spec/go_etcd_io/raft/v3/RawNode__Tick.lean`) already covers a `Tick` that follows any number
of quiesced ticks. Removing the method takes nothing away from what the proofs cover. I did not
write a Lean proof of the old method; the argument above rests on those existing lemmas.

## Build

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results
Proof.github_com.mit_pdos.etcd_grove.examples.register.Results` against the new translation:
succeeds (1907 jobs, no errors). The raft proofs are unchanged and every one goes through.

1582 modules depend on `Code.go_etcd_io.raft.v3`, including etcd's server proofs. I rebuilt only
the raft roots and the register example (the users of raft's `Node`/`RawNode`), not the server's
`Link`/`Results`. Those reach raft only through `Node` and other specs, and none of them names
the removed field. I did not run `etc/tcb-report.py`, because it needs every root up to date;
the axiom comparison is under "Trust base" below.

## Trust base

- New axioms or `sorry`s: none. No Spec or Proof file was added or changed.
- Removed assumption: `RawNode.TypeAssumptions.ptr_TickQuiesced_unfold`, a field of the package
  assumption `go_etcd_io.raft.v3.Assumptions`.
- `#print axioms` of `RawNode.Tick.wp_proof` / the raft `Results` roots: the 331 `#print axioms` outputs of `Proof/go_etcd_io/raft/v3/Results.lean` (including `RawNode.wp_Tick`) are identical, line for line, to those on `lean` (compared from the two builds' `Results.trace` logs); no result reaches `sorryAx`.
- `etc/verified-code.py`: raft's root package loses one function (3 Go lines) in the
  "translated" (unverified) state. Every remaining `RawNode` method has a spec. I did not run the
  script, since it needs a full build.

## Findings

- Bugs in the PR: none.
- Bugs in the existing code: none. Nothing was added to `issues/`.
- Open points (release management, not correctness), from the reviewer:
  1. Semver: raft main is still `module go.etcd.io/raft/v3`. Merged into a v3 minor release
     (3.8), this removes an exported API, against issue #66's v4 plan.
  2. CHANGELOG: the PR predates `CHANGELOG-3.7.md` and `CHANGELOG-3.8.md` and adds no entry.

## Draft review comment

> The removal looks good to me. Nothing in raft (including rafttest) or in etcd calls
> `TickQuiesced`, and the code that uses `Tick` doesn't depend on it: `tickElection` and
> `tickHeartbeat` already handle any value of `electionElapsed`. Two things before merging.
> Since the module is still `go.etcd.io/raft/v3`, is this meant for v4 (as #66 planned), or is
> removing a method deprecated since v3.6 OK in a v3 minor release? Either way, could you add an
> entry for the removal to the changelog of the release it lands in (CHANGELOG-3.8.md, or a v4
> one)?
