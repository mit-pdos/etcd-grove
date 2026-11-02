# Spec review, round 3: the lease-grant stage's design of the server chain (branch `lease-grant`, `7d62260a7c`)

Reviewer: an independent spec reviewer. Read-only: no build and no `lean-check`.

- Target: `notes/lease-grant-plan.md`, "## Design of the server chain (2026-11-02, round 3)". Only the
  diff `7d62260a7c~1..7d62260a7c` was reviewed in depth.
- Round 2: `notes/spec-review/lease-grant-design-r2.md` (of `a2320120fc`).
- Code: line numbers are at `7d62260a7c`.

## Status of round 2's findings

| r2 | status | evidence |
|---|---|---|
| S-A (receive proofs vs the gated `srvRest`) | **fixed** | `applySnapshot.spec`'s pre has `srvRest E γr A` and `lease.lessorRevocable E.γ.leases` (`EtcdServer__applySnapshot.lean:131,134`). `lessorRevocable γl = lessorModeIs γl false` (`InvLessor.lean:449`), and `lessorModeIs γl m = ∃ γr, lessorPinR γl γr ∗ ⌜γr.2.2 = m⌝` (`:441-442`, persistent). With `srvGrantable`'s `lessorModeIs … true`, `lessorPinR_agree` (`:972-979`) gives `γr = γr'`, so `true = false`. The refutation on entry is sound, and it needs no tie. |
| S-B (`mergedObs`, `mergedCreate_window`) | **fixed in substance; one gap** | See S-1 below. `srvBeSnapOk_window` already takes the buckets as an argument (`SnapSendBranch.lean:660-661`), so the window can be restated at the leased buckets. |
| S-C (`certOk` in `newHeader`) | **fixed** | `store.Rev.spec`'s post has `certOk γ log` (`store__Rev.lean`). Because `log' = log`, it is exact. `idxCert` comes from `kvWriter_cert` (`txn/Writer.lean:43`). |
| Q7, Q8 | resolved as recommended | |
| m1 | fixed | `persistTo` and `Revoke` are dropped from commit 2 and from the table. |
| m2 | fixed | The new `lessorBackend` lens is on `Ln` (§2.12). `lessorApplyOk` keeps the `rwLens RW (lessorBeOn …)` premise (`SnapRO.lean:126`). `RW := lessorBeOn lp d.be` is the right instantiation. |
| m3 | fixed, but the law is misstated | See m-a. |
| m4 | fixed | |
| m5 | fixed | |
| m6 | fixed | |

## What is good

- **Placing `srvGrantable` in the leased arm is right.**
  - No frozen text changes. `srvSnapRO` and `isServerM` are untouched.
  - The persistent frame is carried by `srvRest_applyG`, `srvRest_snoc` and `srvGrantOpen`'s body.
  - It is establishable at `NewServer`:
    - the guard is `srvGrantGuard lg on = ⌜leasesNoExpiry ∧ lg ∧ on = false⌝`;
    - `%Hslg` gives `leasesNoExpiry`;
    - `on = false` holds at `lg = true`, now that `specG` at `on = true` takes `lg = false` (m4);
    - `E.lg := ρ.rd.kv.lg` (`NewServer.lean:1166`).
- **The receive side's argument holds with no extra fact.** `applyAll.specSnap` has `γr.kv.lg = false`.
  Its `lessorRevocable` comes from `srvSnapRO`'s `lessorModeIs E.γ.leases γr.kv.lg` (`SnapRO.lean:424`).
  So `applySnapshot` is never entered with the leased arm in a reachable state. The lemmas below it
  (`snap_srvRest`, `SnapApplyRest.lean:37-50`; the walk, which has `lessorRevocable` itself at
  `SnapApplyWalk.lean:142`; `SnapRecvFacts`; `SnapApplyKV`) can take `E.lg = false` as a premise.
- **`lg = false` still reduces to `lean`'s statements.** I checked the changed texts: `srvRest`,
  `mergedObs`, `mergedCreate_window` (`restLeasesWith f [] r = r`), `newHeader` (only a stronger
  post), and `NewServer.specG`/`specM` (a premise that is true at `false`).
- `newHeader`'s post as now written is provable from `Rev`'s spec and `kvWriter`'s exact budget.

## Findings

### Blockers

None.

### Should fix

**S-1. `mergedObs`'s gate is on `γr.kv.lg`, but `mergedCreate_window` has no tie to `E.lg` at
`on = true`, and it is used there.**

- *Principle:* "Sound/complete": the restated window's post must be provable from what its pre holds.
- *Evidence:*
  - §2.14 gates `mergedObs` on `γr.kv.lg`. `srvRest`'s gate is `E.lg`.
  - `mergedCreate_window` is generic in `on` (`SnapSendBranch.lean:535-553`). It is called at
    `on = true` from `applyAll`'s auth-on send branch (`EtcdServer__applyAll.lean:767`).
  - The only `γr.kv.lg = E.lg` fact is in `srvKVInvs` (`InvApplier.lean:342`), and that is
    `srvKVInvsM false` only. `srvKVInvsOn` (`KVApplyOn.lean:299-301`) has no `lg` conjunct.
  - So at `on = true`, the case `E.lg = true` with `γr.kv.lg = false` is not refutable inside the
    lemma. In that case the unfolded `srvRest` gives the leased buckets, but the conclusion asks for
    `bkRestAt` at `restModel`. That is unprovable after a grant.
  - The combination "auth on with `lg = true`" is excluded only at `NewServer` (§2.13), not in
    `isServerM`.
- *Caller affected:* `mergedCreate_window`'s restated proof ("one proof for both arms"), at
  `on = true`.
- *Fix (recommended):*
  - Gate `mergedObs` on a parameter, as `cmp` already is: `mergedObs γr cmp lg ai A log D` with
    `if lg then bkRestAtL … else bkRestAt …`.
  - The three callers pass `E.lg`, beside `E.cmp` (`EtcdServer__applyAll.lean:381`,
    `ApplyAllSnap.lean:458`, and the window's statement).
  - `merged_image` takes `isServer` (`on = false`), so it has `srvKVInvs`' tie and converts to
    `imageAt`'s `γk.lg`.
- *Alternative:* add `γr.kv.lg = E.lg` to `srvKVInvsOn`. That is one more definition changed, and
  one more constructor (the on-mode boot) to prove.
- Either way, update §2.14 and the §3 row for `mergedObs`.

### Minor

- **m-a. `kvLeases_pre` is stated unconditionally, and its justification misnames `pre`.**
  - `(kvLeases γr.kv γr.raft.pre).ids = []` is false for an arbitrary `γr`. It holds where
    `γr.raft.pre = []`:
    - `NewServer.lean:1932`;
    - `runSnapLgOkBody`'s `γn.pre = []` (`InvRun.lean:450`);
    - `SnapRecvFacts.lean:335`.
  - `pre` is the raft node's prefix (`RNNames.pre`, `InvRaftNode.lean:93`), not the boot log.
    `restModel` takes the boot log separately (`γr.raft.raft.boot`).
  - State the law as `γr.raft.pre = [] → …` (then it is `rfl`-level), and drop "the boot log is
    configuration entries".
- **m-b. The window's conclusion needs a leased sibling of `bkRestAt_of_rb`.**
  - `bkRestAt_of_rb` (`InvImage.lean:212-218`) is stated at `(restModel …).bk`.
  - The leased arm needs `rbData P D = (restLeasesWith f T (restModel …)).bk → bkRestAtL …`. The
    same three-line proof works.
  - `srvRestOwn`'s `%Hmi` is about the record's `.mem`. It needs `(restLeasesWith f T r).mem = r.mem`
    (`restGrantT` touches only `bk`).
  - Name both laws in §2.0.
- **m-c. The freeze list's sorry line is inaccurate against the branch.**
  - It says "none beyond those already in the baseline: `srvGrantOpen_open`; `merged_image`; the
    drafts".
  - The branch's `etc/tcb-baseline.txt` has `merged_image` and no `srvGrantOpen_open`. It also has
    none of `EtcdServer.LeaseGrant.wp_proof`, `lessorGrantOkL_of_server` or `leasegrant.Main.wp_proof`.
  - The commit list's own wording ("`tcb-report --check` new only `srvGrantOpen_open` and the
    drafts") is the accurate one. Say that, or update the baseline first.
- **m-d. The freeze list's "text unchanged, definitions underneath changed" is incomplete.** The user
  would want these named too, since their meaning moves at `lg = true`:
  - the auth `EtcdServer.*` specs that name `reqPropOk`/`appliedOkM` (UserAdd, RoleAdd, AuthEnable,
    … : 15 and 6 files under `Spec/go_etcd_io/etcd/server/v3/etcdserver/`);
  - `NewServer.spec` and `examples/compactkv/checkCompactRev.spec` (`kvInv`'s gated fraction);
  - `apply.newAuthApplierV3.spec` (`isApplyLessor`'s Grant clause);
  - `lease.NewLessor.spec` and `applySnapshot.spec` (`lessorApplyOk`).

  None changes at `lg = false`.

Everything else in the freeze list checks:

- One trusted statement changes, `lessorApplyOk`. `Recover`'s spec names it only in a docstring.
- The `rqOk` in `lessor__Renew.lean` is in a docstring.
- The named hypotheses `leasesNoExpiry`, `srvGrantOpen` and `backendUnderQuota` are unchanged. They
  are true of Go as argued in round 2.

## Go code

Nothing new. No bug, nothing for `issues/`.

## Ranking (need of revision)

1. S-1 (`mergedObs`'s gate parameter, or the tie in `srvKVInvsOn`).
2. m-a, m-b (laws to name or restate).
3. m-c, m-d (wording of the freeze list).

## Verdict

The round-3 repairs are sound. The refutation on the receive side checks against the real
statements (`lessorRevocable` is `lessorModeIs … false`, and `lessorPinR_agree` makes the two modes
contradict). `newHeader`'s post is provable as written. At `lg = false` every changed statement
reduces to `lean`'s. One gap remains, S-1: `mergedObs` is gated on `γr.kv.lg`, while the window
lemma runs at `on = true` with no `γr.kv.lg = E.lg` in scope. Gating `mergedObs` on an `lg` argument
that callers pass as `E.lg` (as `cmp` already is) closes it in one paragraph. The minors are wording
and two small named laws. After that edit the design can be frozen and plumbed, with no further
round needed. S-1 also does not block starting commits 1 and 2, which do not touch the send branch.
