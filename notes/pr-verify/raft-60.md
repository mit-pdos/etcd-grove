# etcd-io/raft#60: raft: add backpressure for CommittedEntries flow

- PR: <https://github.com/etcd-io/raft/pull/60> (open, "needs rebase"), head `691a0972eb10e921d85d1440917a108901b478ef`, one commit, by pav-kv.
- Verified at: fork `upamanyus/etcd` branch `pr-raft-60-goose-lean`, commit `a45e525db` (the PR's
  non-test diff against its merge base `7f872e8af`, applied onto `raft37-goose-lean` `509271dac`, the
  pinned raft v3.7 plus the read-index fix), with the PR's two `rawnode_test.go` call-site changes.
- This branch: `pr-verify/raft-60` (worktree `/shared/etcd-grove-pr/raft-60`). Files the report relies
  on: `notes/pr-verify/raft-60/` (README there).

## Verdict

The change is sound as far as verified. With the option off, `ReadyWithOpts` and `readyWithoutAccept`
meet exactly their earlier specs. `Ready()` and `node.run`, now going through them, re-prove their
unchanged specs. With `DisableCommittedEntries` set, the `Ready` carries no committed entries and
everything else is unchanged. The applied-entry bookkeeping stays put (`delivered`/`applying`), so
after a pause the next committed entries handed out are exactly the ones held back: none skipped,
none duplicated. No new axiom or `sorry`.

The one problem is in the API, not in safety. `HasReady()` takes no options. While the only pending
work is paused committed entries it stays `true` forever, so a `for rn.HasReady() { rd :=
rn.ReadyWithOpts(paused); ...; rn.Advance(rd) }` loop spins on empty `Ready`s (Go test below).

Not covered:
- async storage writes (`ownRawNode` requires them off; the reviewer's Go probe shows the paused path is right there);
- liveness (the spec allows any prefix of the next entries, so "resuming eventually delivers" is not proved);
- snapshots pending (outside the spec; `nextCommittedEnts` returns none then anyway).

## Conflicts and rewrites

- `node.go`: one textual conflict next to `isHardStateEqual`. The fork's v3.7 version takes `*pb.HardState`
  and getters; the PR's context line has the gogoproto value version. Resolution: the fork's
  `isHardStateEqual` kept, and the PR's `ReadyOpts` type added before it. No behavior difference.
- `rawnode.go`: applied cleanly onto v3.7's `readyWithoutAccept`. v3.7's body differs from the PR's
  base, which was before the protobuf-go v2 move: pointer snapshot/hard state, `GetTo`. The PR's change
  is only the `CommittedEntries` initializer moving under `if !opts.DisableCommittedEntries`.
- `rawnode_test.go`: the PR's two call-site updates applied by hand, at the fork's line numbers.
- `go build ./...` and `go test ./...` of the fork pass.

## Changed functions

| Function (Go) | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| type `ReadyOpts` (node.go) | new type | — | translated | `go_etcd_io.raft.v3.ReadyOpts` (one `Bool` field), generated instances |
| `(*RawNode).readyWithoutAccept(opts)` | behavior change (new parameter) | verified | verified | new spec, compatible at `ReadyOpts{}` (see below) |
| `(*RawNode).ReadyWithOpts(opts)` | new (exported) | — | verified | new spec: `Ready`'s plus `Hce_off` |
| `(*RawNode).Ready()` | refactor (now `ReadyWithOpts(ReadyOpts{})`) | verified | verified | old spec re-proved, from `ReadyWithOpts`'s spec |
| `(*node).run()` | refactor (passes `ReadyOpts{}`) | verified | verified | old spec re-proved, its proof changed by one argument |

No struct field, invariant or shared-state protocol changes: `ReadyOpts` is a parameter, not node
state.

## Specs

- `RawNode.readyWithoutAccept.spec` (`Spec/go_etcd_io/raft/v3/RawNode__readyWithoutAccept.lean`):
  - Old: no argument. The `Ready`'s committed entries `ce` extend `rs.delivered` (`isCommitted`), plus the node's `ownRawNodeReady` and the messages, entries, read states and hard state handed out.
  - New: takes `opts : ReadyOpts`, with the same postcondition plus `Hce_off : opts.DisableCommittedEntries' = true → ce = []`.
  - Compatibility: the old function no longer exists (its signature changed), so `spec_implies_old` cannot be stated over one program. Instead, the new spec at `ReadyOpts{}` has exactly the old postcondition (one conjunct more), and both callers (`ReadyWithOpts`, `node.run`) are re-proved with it.
- `RawNode.ReadyWithOpts.spec` (`Spec/go_etcd_io/raft/v3/RawNode__ReadyWithOpts.lean`, new):
  `RawNode.Ready.spec` with `opts` and `Hce_off`. With `ce = []` the node's new `delivered` is the
  old one, so the next `Ready`'s entries start where this one would have.
- `RawNode.Ready.spec`: unchanged. Its proof (`Proof/go_etcd_io/raft/v3/RawNode__Ready.lean`) now
  applies `ReadyWithOpts`'s spec. The composition of `readyWithoutAccept` and `acceptReady` moved to
  `Proof/go_etcd_io/raft/v3/RawNode__ReadyWithOpts.lean`.
- Proof of `readyWithoutAccept` (`Proof/go_etcd_io/raft/v3/RawNode__readyWithoutAccept.lean`): the
  `if` is joined (`wp_join ... at next`, cases on the flag) at "some `ce`, a prefix of the next
  committed entries, empty if disabled". The disabled arm gives `nil` (`entsPts_nil`,
  `ownSliceCap_nil`). The rest of the proof is unchanged.

## Callers (step 6)

- `readyWithoutAccept` ← `ReadyWithOpts` (re-proved), `node.run` (re-proved, spec unchanged: stop).
  `node.run` always passes `ReadyOpts{}`, so the `Node` API (`node.Ready()`) is unchanged and does not
  offer the option.
- `ReadyWithOpts` ← `Ready` (re-proved, spec unchanged: stop). It is also a new exported API: its
  callers are applications, and the change is user-visible as an addition only.
- `Ready` ← applications, and etcd's server through `node`, not `RawNode`: unaffected.
- Not rebuilt: etcd's server proofs (`Proof/go_etcd_io/etcd/server/...`, which import the raft `Link`).
  They use `node.Ready.spec`, whose statement and proof are unchanged.

## Trust base (step 7)

- Built: `Proof.go_etcd_io.raft.v3.Link` and `Proof.go_etcd_io.raft.v3.Results` (1839 jobs). This
  rebuilt every raft proof, since the regenerated `Code/go_etcd_io/raft/v3.lean` changed.
- `etc/tcb-report.py` was not run: it needs a full build of the worktree.
- Instead, `#print axioms` of `RawNode.wp_ReadyWithOpts`, `wp_Ready`, `wp_readyWithoutAccept` and
  `node.wp_run` were compared with `lean`'s (`notes/pr-verify/raft-60/print-axioms.{lean,log}`): the
  axiom sets are identical, and none has `sorryAx`.
- New postulates: none. New `sorry`s: none.
- Collection `etc/tcb-collections/pr-raft-60.txt` has the roots; its baseline is still to be written
  with `--check --update` after a full build.

## Findings (step 8)

1. **`HasReady` ignores `ReadyOpts`** (PR; medium, API). `HasReady()` reports a `Ready` whenever
   committed entries are pending, so with the flow paused it is `true` forever and every `Ready` is
   empty. The PR's doc comment does not mention it, and there is no `HasReadyWithOpts`.
   - Test: `TestReadyOptsHasReadyIgnoresOpts` in `notes/pr-verify/raft-60/rawnode_readyopts_test.go`, at the PR head. After 100 paused `Ready`s (99 empty), `HasReady` is still `true`.
   - The fork version is in `notes/pr-verify/raft-60/fork/`.
2. **Pausing also stops the leader's uncommitted-size budget from being released** (PR; low,
   undocumented). In v3.7 the leader's uncommitted-size count drops only when entries are applied.
   - Effect: while paused, proposals are dropped (`ErrProposalDropped`) once `MaxUncommittedEntriesSize` is reached, even though everything is committed and persisted. They are accepted again after resuming.
   - Reviewer's probe: `TestReview60UncommittedBackpressure` in `notes/pr-verify/raft-60/fork/rawnode_review60_test.go`. Proposal 4 was dropped at committed=5, applied=1.
   - Probably intended (it is backpressure), but worth a sentence in the doc.
3. **Conf changes stall while paused** (PR; low, informational). With `pendingConfIndex > applied`, a
   second conf change is proposed as an empty `EntryNormal`. A node with an unapplied conf change does
   not campaign. This is how a slow apply already behaves, but the option makes the state easy to hold
   indefinitely.
   - Reviewer's probe: `TestReview60ConfChangeBlocked`.
4. Checked and correct:
   - **Async storage writes:** paused `Ready`s carry no `MsgStorageApply`, and entries 1..14 were applied once and in order with `MaxCommittedSizePerReady=1` (`TestReview60Async`).
   - **Pause then resume, no gap and no duplicate:** `TestReadyOptsNoGapNoDup`.
   - **`Advance` after a paused `Ready`:** it does not touch `applying`, since `acceptReady` calls `acceptApplying` only for non-empty entries. This is proved.
5. No bug in the existing (pinned) code was found, so nothing was added to `issues/`. No `issues/`
   finding is about this code path.
6. The PR adds no test of its own.

Reviewer (fresh subagent): no open points beyond the above. It noted that the spec allows `ce = []`
even with the option off: an existing liveness gap, not a spec change.

## Draft review comment (for the user to edit and post)

> I went through this change carefully, including running it on top of the v3.7 code. With the
> option off, behavior is unchanged. With `DisableCommittedEntries`, a `Ready` carries no committed
> entries and nothing else changes. `acceptReady` leaves the applying index alone, so the entries
> held back are exactly the next ones handed out on resume, with no gap or duplicate. That also holds
> with `AsyncStorageWrites` (no `MsgStorageApply` while paused).
>
> A few things worth addressing:
>
> 1. `HasReady()` doesn't know about the options. While only committed entries are pending, it stays
>    true, so a typical `for rn.HasReady() { rd := rn.ReadyWithOpts(paused); ...; rn.Advance(rd) }`
>    loop spins on empty `Ready`s. Could there be a `HasReadyWithOpts(opts)` (or the options kept on
>    the `RawNode`), or at least a note in the doc comment?
> 2. While paused, the leader's uncommitted-entries budget isn't released (it shrinks only as entries
>    are applied), so proposals start failing with `ErrProposalDropped` once
>    `MaxUncommittedEntriesSize` is reached. Similarly, a pending conf change blocks further conf
>    changes until applied. Both may be intended backpressure, but they'd be good to mention in the
>    `DisableCommittedEntries` comment.
> 3. A test of the new option would help, e.g. pause for a few `Ready`s, resume, and check that every
>    committed entry comes out once and in order.
>
> The option isn't reachable through `Node` (`node.run` always passes `ReadyOpts{}`). Is that
> intended for now?
