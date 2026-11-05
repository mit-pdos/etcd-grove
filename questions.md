# Questions and pending decisions (lease-expiry, worktree /shared/etcd-grove-leaseexp)

Relayed by the user's session; answers come back by message.

## Q1 (2026-11-05): confirm the three approvals given through AskUserQuestion
The user approved, through the coordinator's AskUserQuestion dialog (recorded in
notes/lease-expiry-plan.md, "Decided (the user, 2026-11-05)"):
1. `lease.NewLessor.wp_proof`'s post gains `lease.leaseEver γl ∅` (E3 (c), route A);
2. E2 revision 5, the restated trusted `EtcdServer.leaseTimeToLive.spec`;
3. `etc/bounds-baseline.txt` +1 spec-thread / +2 spec-receipt (leaseexpiry `Main.spec`).
The Part E agent declined to act on them as relayed. The coordinator is proceeding on them
(they are the user's own answers); a veto here stops the work that uses them.
Depends on it: E2's application, E3 (c) stages 1-2, `Main`'s proof and link, trust base 785/7.
Recommendation: confirm.
**Confirmed by the user 2026-11-05** (relayed by the user's own session): all three stand.

## Pending before Freeze (hard stop)
- `axiom` skill on: `schema.MustUnsafeGetAllLeases.wp_proof` (new), `lease.NewLessor.wp_proof`
  (widened post), restated `leaseTimeToLive`, restated `lessorExpiredC`.
- P1: the Perennial thread-tokens-by-level change (upstream: a hard stop) to discharge
  `srvRevokeOpen_open`.

## Decided by the agent, pending the user (2026-11-05, E2 rev 5 / E3 (c) application)
Each recorded with its options and evidence in notes/lease-expiry-plan.md, "Applying E2 rev 5 and
E3 (c) (2026-11-05)"; the agent proceeds on its recommendation.
- A1: `leaseTTLRow`'s typing: the cluster is a server raft's (`∃ γ : SrvRaft`, `γ.cl`, at
  `srvStor γ`), since `nodeStartedFresh`/`isCommittedLogLb`/`confAt` need a storage model.
- A2: `histIn` counts an item map's ids too (`snapHas`: in the lease map or attached to an item).
- A3: the row's lessor `γl` and the built server's `E.γ.leases`: `lease.srvInv` (sealed, in
  `memberBuilt`/`memberUp` through `srvLeaseRd`) gains `lessorAt E.γ.leases 0 (∅, ∅, ∅)`;
  `BuildServer`/`StartServer` return the row's raft part `leaseTTLRowR s ps` as their own conjunct,
  and `leaseTTLRow_intro` makes `leaseTTLRow s γl` from it at `ps = [x]` and that snapshot.
- A4: "in the revocable mode `id ∉ U`" stated mode-free: `Grant` takes
  `lessorModeIs γl true ∨ ⌜id ∉ U⌝`.
- A5: `Recover` takes and returns `⌜recs = []⌝ ∨ leaseEver γl U` (its one call recovers nothing).
- A6: the apply thread's U is among the revocable grant ids of the applied entries with data.
- (Information) the one-prefix fact is proved (no premise): the single-member cluster's
  allocation fixes the generator's prefix in the revocable mode.

## (Coordinator's request, 2026-11-05) Placement of the lease-TTL row
- A7 (decided by the agent, pending the user): the row's raft part (`leaseTTLRowR`) stays a
  separate first-start conjunct of `NewServer.specG`, `BuildServer.spec` and `StartServer.spec`
  for now, not in the lease slot. Options: (a) inside `lease.srvInv` — not possible: `srvInv` is
  also in the restart contracts' posts (`BuildServer.specRestart`'s `memberBuiltR` →
  `memberBuilt` → `srvLeaseRd`), where `nodeStartedFresh` is false; (b) a first-start-only lease
  fact in the lease slot (a flag on `srvLeaseRd`/`memberBuilt`/`memberUp`, `true` only on the first
  start) — the right home once hub step 7 removes starter conjuncts, but it changes
  `memberBuilt`/`memberUp`'s signature in every example while another agent of this stage is
  editing them (the read layer's registrations); (c) keep the conjunct (done; already threaded
  through `newServerMode`/`newServer`/`BuildServer`/`StartServer`). Recommendation: (c) now, (b)
  with hub step 7. The trusted text is unchanged either way; the docstring's "Returned by
  `BuildServer`'s and `StartServer`'s first-start postconditions" stays accurate under (c).

## HARD STOP at Freeze: the sorry `srvRevokeOpen_open`
- What: `theorem srvRevokeOpen_open : srvRevokeOpen` (`EtcdServer__run.lean:289`), a marked
  `sorry`: the open case of a revocable-lease cluster (`EtcdServer.revokeExpiredLeases.spec`,
  `run`'s expiry arm). New on `lean` (trust base 6 → 7 sorries).
- Which results reach it: only leaseexpiry's (`etcd_leaseexpiry.wp_Main` and its MainLinked/Results
  roots; `run` takes the case as `lease.runCfg`'s revocable conjunct, so no other result does). The
  exact list from `etc/tcb-report.py --roots` is added here once leaseexpiry's `Main` is linked.
- Why it cannot be discharged now: P1. `revokeExpiredLeases` (`server.go:860`) calls
  `ensureLeadership` and `GoAttach`es one goroutine per round of expired leases; `GoAttach.spec`
  gives the goroutine only `P` and takes back `True`, but each goroutine needs a thread token plus
  `wgMu`'s, the logger's and the read loop's reader slots, and rounds are unbounded (an unrevoked
  lease is re-sent each retry interval). The general fix is thread tokens by level
  (`threadTok ⊣⊢ [∗ l < L] levelTok l`, a counted wait group taking `levelTok 0`).
- P1's design status: only the entry in `notes/perennial-changes.md` ("Thread tokens by level",
  2026-11-04); no Perennial branch exists (a Perennial change is a hard stop for this stage).
- Options: (a) land the sorry (approved in principle 2026-11-04 and 2026-11-05; final decision at
  Freeze); (b) keep leaseexpiry's `Main` and its link off `lean` until P1 lands.

## `nodeStartedFresh` in raft's API (decided by the agent under E2 rev 5, pending the user)
- `StartNode.spec`'s post gains `nodeStartedFresh n γ N vs ctxs cv.ID'` (sealed, `InvNodeRule`,
  importable per `etc/api/raft.txt`), with the raft-internal `nodeDriverFrom` it is built from
  (since the review, the start tag `nodeStartTag`: next section but one);
  the regenerated `interface/` diff is in the stage's commits. To be reviewed in the axiom/review
  pass.

## Freeze decisions (approved by the user, 2026-11-05, via etcd-grove-82)
- `srvRevokeOpen_open`: option (a), land with the gated sorry; trust base 6 → 7 sorries
  (`etc/tcb-report.py --check --update`), the leaseexpiry collection.
- A7 (the lease-TTL row's placement): option (c), the starter conjunct for now; hub step 7 moves
  it into the lease slot.
- The four axiom reviews (NewLessor with `leaseEver ∅`, `MustUnsafeGetAllLeases`,
  `leaseTimeToLive` rev 5, `lessorExpiredC`) survived; their commits are cherry-picked onto
  `lease-expiry`.
- `nodeStartedFresh`: reviewed by a fresh spec-reviewer (the coordinator's); its findings are in the
  next section.

## `nodeStartedFresh`: the spec review's findings (2026-11-05, `/shared/tmp/review-nodeStartedFresh.md`)
No first-tier finding: `nodeStartedFresh` holds of every node `StartNode` makes, and no node
`RestartNode` makes has it. What was done with each finding:
- **N1, N2, D1, D2, D3, D4 (decided by the agent, pending the user: a statement change).**
  - *The question.* The start record was a 6-tuple of driver state (`nodeStartRec`), compared
    against `NodeDriverState.init`. Its exclusion of restarts rested on two things:
    `RestartNode` discarding its record, and a `[scope]` premise marked for removal. A
    `RestartNode` on an empty storage (etcd's join without a WAL, `bootstrap.go:516-517`) would
    have given `init`'s record.
    - D1: the record's `⌜γn.stor = st.storage⌝` conjunct was vacuous.
    - D2: "a lower bound of the loop's states" was unproved.
    - D3: the docstrings said `RestartNode` records its restart state.
  - *Options.*
    - (a) Keep the state record and fix the docstrings.
    - (b) Record a tag instead: N1, the reviewer's recommendation.
  - *Recommendation and what was done.* (b), because it is small. `ApiImpl.nodeStartTag n γ boot`
    (`InvApi.lean`; replaces `nodeStartRec`/`nodeDriverFrom`) is
    `∃ γn, nodeTabOk γ n γn ∗ dghostVar γn.start □ boot`, a write-once record of the start:
    - `StartNode` writes `true`.
    - `RestartNode` writes `false` (persisted, then dropped).
    - `nodeStartedFresh := isNode ∗ nodeBoot ∗ ⌜id ∈ vs⌝ ∗ nodeStartTag n γ true`.
    - The docstrings (`InvApi`, `InvNodeChan`'s `NodeNames.start`, `InvNodeRule`) now say this.
  - *Evidence.* `StartNode`, `RestartNode`, raft's API modules, `Link`/`Linked` and the server and
    etcdstart links build. `nodeStartedFresh`'s signature is unchanged and its body sealed, so
    `interface/` does not change (regenerated: 0 files).
- **N3 (preference): no elimination laws.** None added: the trusted spec is the only consumer. Add
  them (`→ isNode`, `→ ⌜id ∈ vs⌝`) when a second consumer appears.
- **S1: `interface/` stale.** Regenerated in `01cfcabf20` (`StartNode`'s post, `def (sealed)
  nodeStartedFresh`, its instance). After N1, regenerated again: no diff.
- **S2: `StartNode.spec`'s docstring.** Reworded: "The post is `RestartNode.spec`'s, plus …
  `nodeStartedFresh`".
- **C1 (preference): keep the raft-API fact rather than a server-local token.** Kept.
- **The Go doc gap.** `StartNode` on a non-empty storage only logs `Bootstrap`'s error and runs the
  node as a restart (`node.go:258-261`). Recorded in
  `nonissues/raft-startnode-nonempty-storage-silent-restart.md` (`blocks-proof: no`: etcd never
  does it, and `StartNode.spec` takes an empty storage).

## Hub requests
- **H-a (approved by the user, 2026-11-05, via etcd-grove-82):** `leaseTTLRow` is, for now, a
  separate conjunct of the starters' postconditions that holds only on a first start (option (c)).
  It moves into the lease slot with hub step 7.
- **H-b (approved by the user, 2026-11-05, via etcd-grove-82):** the lease slot in `NewServer`
  (binder `m : lease.Mode`, premise `lease.bootCfg`, postcondition `lease.srvInv`) is accepted.
- `nodeStartedFresh` is a change to raft's API, not to a hub. Its review findings are in the
  section above.
- Landing goes only through `etc/land.sh`: after merging `lean`, and only once the coordinator says
  go. Never fast-forward `lean` by hand, and never wrap `land.sh` in `flock`. The restart branch
  `r2b3` is adding a sealed stop slot (`srvStop.keep`, `StopApi.lean`) next to the lease slot in
  `NewServer`'s postcondition; whichever branch lands second resolves that conflict.
