# Spec review: lease-mono3, round 3 (after merging `lean` with R2c)

Reviewer: independent subagent, 2026-11-06. Branch `lease-mm` at `933df7bb1c` (worktree
`/shared/etcd-grove-leaseexp`). The merge is `b1d0f637f7`, with parents `64aca75ad9` (round 2's
fixes) and `6b49f77e01` (`lean`, R2c Freeze). Their merge base is `71c9d0ee60`. Two commits follow
the merge: `68e4e8e89d` (StartMember drops `memberUp`'s stop right) and `933df7bb1c` (leasecatchup's
collection). I changed nothing in the repository apart from this file.

Commands run, none of which builds:
- `lake build --packages=/shared/tmp/manifest-84d.json --no-build` on leasecatchup, partition,
  putget3 and k8s compactor `Results`, and on `restart.Run`. It printed "All targets up-to-date
  (7844 jobs)" and exited 0.
- `etc/tcb-report.py --check --reuse`, over `.lake/tcb.json`. That file was computed at
  `68e4e8e89d`, and HEAD differs from it only in `etc/tcb-collections/leasecatchup.txt`. The main
  baseline and the leasecatchup, linkv3p, k8scompactor, putget3, leasekv and leaseexpiry collections
  all match.

**No BLOCKER, no SHOULD-FIX of the specs.** R2c's change needs no change to a lease-mono3 statement.
The merge is clean: the two sides touched disjoint files in `examples/lib`. The new collection lines
are exactly the six that `lean` added to every server collection. What is left: two process items
(P1 carried over, P3 new) and NITs.

## 1. Does a lease-mono3 statement need to say more after R2c?

**No.** `StartMember.lean:163-164` drops `memberUp`'s last conjunct with the trailing `-`. That
conjunct is `∃ dd, srvStopRight s E ρ.rd.raft.raft ρ id dd` (`etcdstart/Defs.lean:357-358`).
Dropping it is right, and it is what `lean` itself does:

- **`lean`'s own cluster3 drops it too.** At `6b49f77e01`, `cluster3/StartMember.lean:135-136` ends
  its `icases` with `HWR, -⟩`. At `.none`, that `-` swallowed `srvLeaseRd s E .none ∗ ∃ dd,
  srvStopRight …`. The branch names `#HLR` (the lease reader it needs at `.mono`) and adds one `-`,
  so it drops exactly the conjunct `lean` dropped. Partition, putget3 and the k8s compactor reach
  `memberUp` only through cluster3 or their own unfolds (`putget3/Main.lean:282,309,335`), and none
  of them keeps the right. Restart is the one consumer of the right. It does not use cluster3: it
  uses its own `startMember` and `memberUp_stopRes` at `.none` (`restart/Defs.lean:160-166`,
  `Run.lean:307,330`).
- **A served member cannot be stopped.** `EtcdServer.HardStop.spec` takes `srvStopRight ∗
  srvStopReq`, and `srvStopReq` includes `srvStopReaders E` (`InvRestart.lean:240-241`). Those
  readers are the 64 `storeReader`s and watch readers that `cluster3.StartMember` hands to
  `v3rpc.Server`/`Serve`, and no spec gives them back. The HardStop header (`Spec/…/
  EtcdServer__HardStop.lean:10-15`) says so: "a member can be stopped only if it never served".
  `srvStop.scope` also requires `cmp = false`, while cluster3 runs at the cluster's `cmp`. So
  carrying the right in `memberServed` would hand callers a resource they cannot use.
  `EtcdServer__Start.lean:41` already says that a caller that never stops drops it.
- **It could not go into `memberAt` anyway.** `memberAt` is persistent (`memberAt_persistent`,
  `cluster3/Defs.lean` after `memberAt_none`), and `srvStopRight` is exclusive.
- **No Go caller stops a member.** `examples/lib/cluster3/cluster3.go`,
  `examples/etcd/leasecatchup/leasecatchup.go` and the partition example call no `Stop`/`HardStop`
  (grep). Under "Complete: every caller", nothing is missing.
- **The other R2c changes do not touch the branch's statements.** Those changes are the `Start.spec`
  and `start.spec` posts and `memberUp_stop`. `kv_lease_served_watch`
  (`etcdstart/ServedLease.lean`), `servedRegs`, `memberServed`, `memberAt`, `clusterAt` and
  `clusterUp` do not mention `memberUp`'s last conjunct. The leasecatchup specs, `Adequacy` and
  `Results` are byte-identical to `64aca75ad9` (`git diff 64aca75ad9 HEAD` over
  `{Spec,Proof}/…/leasecatchup` is empty).
- **`memberUp_stop` is a law over a free mode `m`, and it holds at every `m`.** It only drops
  `srvLeaseRd s E m` and other affine resources, and its pure conclusions (`authOn = false`,
  `E.cmp = E₀.cmp`) come from `memberUp`'s `HEc`, which does not depend on the mode.

## 2. Do the merged files say what both parents say?

**Yes.**
- **Disjoint files in `examples/lib`.** Over `{Proof,Spec}/…/examples/lib` and `interface/`, the two
  sides changed no common file:
  - `lean` changed etcdstart's `Defs`, `NewMember`, `Restart`, `Start`, `StartServer`, `StartStop`,
    `newServerMode`, `BuildServer` and `newServer`.
  - The branch changed cluster3's `Defs`, `Link`, `StartCluster`, `StartMember` and `holdToken`, and
    etcdstart's `Alloc3`, `Served` and `ServedLease`.
  - `git diff lean HEAD` there touches only the branch's files, and `git diff 6b49f77e01 HEAD` none
    of `lean`'s.
- **Every file changed on one side only is that side's version in the merge** (checked file by file).
- **The eight files both sides changed:**
  - `restart/Run.lean`: both sides' hunks are present, with 26 changed lines against each parent.
    The branch's hunk adds `.none lease.runCfg_none (by decide)` to `alloc3` and an `isimp … at
    Hetcd`. `lean`'s adds `memberBoot_cmp` and `memberUp_stopRes`.
  - `etc/gen-init.py`: the branch's `leasecatchup` entries in `ROOTS`/`PROGRAMS`, and `lean`'s
    rpctypes descriptions.
  - `etc/bounds-baseline.txt`: the branch adds the leasecatchup rows and etcdstart's stock (23 to
    24). `lean` lowers etcdserver's stock (36 to 35).
  - `linkv3p.txt` and `k8scompactor.txt`: the branch's `leaseTimeToLive.wp_proof` and
    `sort.Sort.wp_anyLess` (P1), and `lean`'s six additions.
  - Notes.
  - None of these resolutions changes a statement.
- **`StartMember.lean:164` is the one change after the merge**: the planned edit
  (`lease-mono3-plan.md:418-421`, §6:133). The merge commit `b1d0f637f7` itself does not build (N2).

## 3. The trust-base changes

**Consistent.**
- **Exactly `lean`'s six additions.** `933df7bb1c` adds `rpctypes.ErrGRPCCompacted_init`,
  `ErrGRPCFutureRev_init`, `apply.memberEnc_id_learner`, `apply.memberKey_inj`,
  `lease.lessor.Stop.wp_proof` and `membership.membersOf_decode` to
  `etc/tcb-collections/leasecatchup.txt` (`:68, :71, :257-258, :470, :481`). These are the six
  lines that `lean` added between `71c9d0ee60` and `6b49f77e01` to linkv3p, leasekv, leaseexpiry and
  putget3, with no removals.
- **Why every server collection carries them.** The three configuration axioms and `lessor.Stop`
  come from R2c's single `run.spec` (`a3a9cf1236`: "785 -> 788 … also lease.lessor.Stop.wp_proof",
  approved by the user per STATUS). That is why collections that never stop a member carry them.
- **leasecatchup's axioms are a subset of linkv3p's.** The set difference leasecatchup ∖ linkv3p is
  empty. linkv3p ∖ leasecatchup is the bridge's `Blackhole`/`Unblackhole`/`DropConnections`, the
  watch stream's client side (`grpc.ClientConn.NewStream`, `GenericClientStream.*`,
  `streamKeyFromCtx`, `context.WithCancelValCtx`) and `proto.Clone`. leasecatchup cuts peers rather
  than bridges and opens no watch, so that difference is plausible.
- **`--check --reuse` passes**: 630 axioms and 0 sorries, and the main baseline has 790 axioms and 3
  sorries. This closes round 2's P2.

## Findings

### SHOULD-FIX (process)

- **P1 (carried over from r1 §1 and r2): the user's acknowledgement is still owed.**
  `etcd_partition_safe` and the k8s compactor's results gain `EtcdServer.leaseTimeToLive.wp_proof`
  and `sort.Sort.wp_anyLess` (`git diff lean HEAD -- etc/tcb-collections/{linkv3p,k8scompactor}.txt`).
  This is unchanged by the merge. Restatement: at Freeze, as in r2.
- **P3 (new; the record): the notes still say P2 is open.** `notes/lease-mono3-plan.md:623-624`
  still says P2 is "still open". The plan has no entry for the merge and its two follow-up commits.
  STATUS's newest entry is round 2's fixes. Restatement:
  - Add a "Merge of `lean` (R2c, 7c-1b)" note to the plan: the trailing `-` at
    `StartMember.lean:164`, the six collection lines, and P2 closed.
  - Add a STATUS entry for it before landing.

### NIT

- **N1 (Know the margin).** Neither `cluster3.StartMember`'s spec header (`Spec/…/cluster3/
  StartMember.lean:1-21`) nor `memberServed`'s docstring (`cluster3/Defs.lean:187-196`, "reduced to
  what a cluster's user needs") says that the stop right `Start` gives is dropped. The code returns
  `s`, on which Go could call `Stop()`. Restatement, one sentence in the header: "`Start`'s right to
  stop the server (`srvStopRight`, `memberUp`'s) is dropped: a served member cannot be stopped
  (`EtcdServer.HardStop.spec`'s header), and no cluster3 client stops one."
- **N2 (bisectability).** `b1d0f637f7` does not build. Its `StartMember.lean` ends the pattern
  `#HLR⟩`, which would bind a non-persistent `srvLeaseRd ∗ ∃ dd, srvStopRight` (the plan says so,
  `:418-421`). `68e4e8e89d` repairs it. `etc/land.sh` gates only HEAD, so this matters only for
  bisecting. No action needed beyond knowing it; next time, fold the fix into the merge commit.
- **N3 (pre-existing: every unfold is a missing law).** The merge needed a proof edit only because
  `cluster3.StartMember` destructures `memberUp` positionally (`iunfold memberUp`,
  `StartMember.lean:162-164`), as `lean`'s putget3, txnlin, leasegrant and leaseexpiry do. R2c added
  an elimination for the stop side (`memberUp_stop`) but none for the serving side, so each new
  conjunct of `memberUp` breaks every server-side unfold again. Restatement: an etcdstart law
  `memberUp_serve` (`memberUp … m ⊢ ∃ E cfg γw, ⌜…⌝ ∗ isServerReq … ∗ … ∗ srvLeaseRd s E m`), used by
  cluster3 and the single-member examples. This is etcdstart's debt, not this stage's.
- r2's N3 (a `clusterUp` elimination) stays left, with the reason in the plan (`:619-622`).

## Ranking by need of revision

1. **Notes and process**: P3 (record the merge and close P2 in the plan and STATUS), then P1 at
   Freeze.
2. **`cluster3.StartMember` (spec header)**: N1, one sentence.
3. **etcdstart's `memberUp` API (pre-existing)**: N3, outside this stage.
4. **`memberServed`, `memberAt`, `clusterAt`, `clusterUp`, `servedRegs`, `StartCluster.spec`,
   `kv_lease_served_watch`, leasecatchup specs and `Results`, collections**: no revision. R2c leaves
   them correct, the merge left them as the branch had them, and the collections match `lean`'s
   additions.
