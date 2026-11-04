# Spec review, round 2: the lease-grant stage's design of the server chain (branch `lease-grant`, `a2320120fc`)

Reviewer: an independent spec reviewer. Read-only: no build and no `lean-check`.

- Target: `notes/lease-grant-plan.md`, "## Design of the server chain (2026-11-02, round 2)", lines
  316-689. Paragraphs are cited as §N.M.
- Round 1: `notes/spec-review/lease-grant-design.md` (of `5cc0eaa28a`).
- Code: line numbers are at `HEAD` (`a2320120fc`) of `lease-grant`.
- Go: the pin `/shared/etcd-goose-lean-wk` (`09669450f`).
- Judged by: `PRINCIPLES.md` and the examples `compaction-in-place.md`, `apply-loop-merge.md` ("check a
  'callers untouched' claim against the order the caller's proof obtains its facts") and
  `compact-client.md`.

I checked the round-2 repairs against the callee statements on the branch and the Go code. Most of
them hold:

- B1 is fixed: `∃ f`, TTL-free.
- S2 (the mode for `leaseGrantedAt`) is fixed.
- S3 (`srvRest_applyG`'s premise) is fixed.
- The token argument of the strengthened `newHeader` is right.

The repairs leave three gaps, each a paragraph to fix. None makes a statement false, and nothing in
`srvGrantOpen` is false of Go as far as I can check. So there is no blocker.

## Status of round 1's findings

| r1 | status at `a2320120fc` | evidence |
|---|---|---|
| B1 (`mt` in the shared image) | **fixed** | `srvRest` and `bkRestAtL` are over `∃ f` (§2.9, §2.14). The member's TTL is only in `Grant.spec`'s `∃ mt` (`lessor__Grant.lean:57-58`, unchanged). The Grant clause gives `∃ t`. The truth of `srvGrantOpen` no longer depends on the members' `minLeaseTTL` (below). |
| S1 (header) | **fixed in substance; one conjunct missing** | See S-C below. |
| S2 (mode) | **fixed** | `srvGrantable` and `grantPermRq` carry `lessorModeIs … true`. `leaseGrantedAt_of_live` (`InvLessor.lean:488-490`) then applies in the backend triple. |
| S3 | **fixed** | §2.9's premise is `plainCover rq ∨ grantPropOk E.lg rq`. `grantKindOk` (`Chain.lean:253-256`) excludes `noSideEffect` and admin. |
| S4 | **fixed for `imageAt`; incomplete** | The second carrier of `bkRestAt`, `mergedObs`, is not gated. See S-B. |
| S5 | **mostly fixed** | The §3 table exists. It misses the snapshot-receive proofs and the send window (S-A, S-B). |
| M1 | **fixed**, two inaccuracies | See m1. |
| M2-M5 | fixed | M5's claim checked: `rangeReadOkM`'s serializable arm has no `Q` (`ReadOn.lean:163-171`). |

## What is good

- **The TTL-free image is the right shape.**
  - `restLeasesWith f ids` over `restGrantT` keeps the record format `leaseEnc id t 0` and abstracts
    only the TTL. That TTL is the member-dependent value: `lessor.go:301-303` raises it to the
    member's `minLeaseTTL`, and `lease.go:55-61` persists it.
  - The remaining TTL 0 is right for this scope:
    - Go's `Grant` stores `remainingTTL` 0.
    - The only other writer, `Checkpoint`, is reached only through a `LeaseCheckpoint` entry, which
      `rqOk` excludes (`Chain.lean:281`).
    - `Promote`/`Demote`/`Renew` do not persist.
  - `restLeasesWith_snoc` with `Function.update f id t` needs `id ∉ ids`. The triple gives that
    (`grantIdsOk`).
- **`srvGrantOpen` (`runSnapLgOkBody`, `InvRun.lean:443-479`) is now plausibly true of Go.** After a
  received snapshot:
  - the follower's lease bucket holds the leader's records for the ids of `kvLeases` of the same
    committed log (`∃ f` absorbs the leader's TTLs);
  - `Recover` rebuilds the lessor's map from those ids;
  - the table is monotone in the log, because revocations and checkpoints are out of `rqOk`, and
    `leasesNoExpiry` means the expiry loop proposes nothing. So the history stays monotone.

  I found nothing else in the body that names a member-local value.
- **The strengthened `newHeader.spec`'s token argument (§2.11a) is right.**
  - `kvWriter` holds exactly `soleBudget log = 2^63 − 3 − |log|` tokens (`SoleWriter.lean:55, 89-91`,
    unfolded in the present proof, `applierV3backend__newHeader.lean:60-62`).
  - `store.Rev.spec` (`store__Rev.lean`) returns `log <+: log' ∧ |log'| + m + 3 ≤ 2^63` and
    `v = W64(|log'| − 1)`.
  - With `m = soleBudget log`, `|log'| ≤ |log|`, so `log' = log` and `|log| + 3 ≤ 2^63`. When
    `|log| > 2^63 − 3`, the truncated budget is 0 and the bound contradicts `log <+: log'`.
  - `2 ≤ |log|` is `soleLog` (`SoleWriter.lean:62`).
  - So `sint.Z rv = |log| − 1`, and `rv ≠ 0`. `srvRevLb` (`CompactMode.lean:57`) needs `rv < |log|`,
    which holds.
  - Go's `newHeader` reads `KV.Rev()` once, after `Grant`, which changes no KV log
    (`backend.go:83-92, 306-314`).
- **`lessorApplyOk`'s new text is true of Go and gives out nothing counted that it did not take.**
  - `persistTo(le.b)` reads the field under `le.mu` before `BatchTx()` (`lease.go:55-61`, from
    `lessor.go:312`). `LockInsideApply`/`Unlock` do not touch `le.b`.
  - So the lent part `Ln` is returned. The counted `wbTok` is still the `T` that `LockInsideApply`
    takes (`LessorBackend.lean:84-87`).
  - On Grant's early-return arms (`lessor.go:282-299`), `T` is dropped, as today. This is
    conservative.
  - The derived chain works:
    - `isApplyLessor_of_lessorInv` (`LessorDerive.lean:246-330`) instantiates `Ln :=
      lessor.lessorBeOn lp d.be`.
    - The RO lens it already takes (`:262-265`) supplies `Ln` and `storeRb γ rs.bk`, and recloses
      `RO {rs with bk := rbSet …}`.
    - The Checkpoint clause still gets `Ln` from `RW` (`srvRestRWH_lessor`, `SnapRO.lean:138-148`).
- **`srvGrantable` is establishable.**
  - `NewServer` installs the guard `srvGrantGuard ρ.rd.kv.lg on` (`NewServer.lean:585`), which is
    `⌜leasesNoExpiry ∧ lg ∧ on = false⌝` (`InvApplier.lean:481-482`).
  - `leaseGranted γl id = ∃ GA, lessorGuard γl GA ∗ □ GA id` (`InvLessor.lean:619-620`).
  - So at `lg = true`, with `%Hslg` and auth off, `∀ id, leaseGranted` holds.
  - The mode conjunct is already in `srvSnapRO` (`SnapRO.lean:424`), given the tie.
- **The success/failure equivalence matches the model.**
  - The triple's `err = nil ↔ grantGoes c rq ∧ grantIdsOk T g.id g.ttl` is `backendTable`'s
    `leaseGrantOk` (`KVModelDefs.lean:287-288, 345-350`) composed with `chainTable`.
  - `cappedRejects`/`corruptRejects` both list `.leaseGrant` (`Chain.lean:137-145`), as
    `capped.go:44-46` and `corrupt.go:49-51` reject it.
  - Quota passes `err` through under `backendUnderQuota` (`quota.go:54-61`).
- **Q3 (a) is argued correctly.** In (a′) the backend triple must update a half that would sit inside
  the abstract `E.RO`. That needs a lens `AEnv` does not have, or a new `isApplyLessor` argument.
  (a) keeps the halves in the open.

## Findings

### Blockers

None.

### Should fix

**S-A. The snapshot-receive proofs unfold the gated `srvRest` (and build `leasesLive`) with no
`lg = false` fact in hand. "Receive: unchanged" (§2.14) and the §3 row "`srvRest` … gated: `_false`
by `rfl`/`simp`" do not hold for them.**

- *Principle:* "check a 'callers untouched' claim against the order the caller's proof obtains its
  facts" (`apply-loop-merge.md`); `compaction-in-place.md` (the old meaning as a law the callers
  can use).
- *Evidence:*
  - `EtcdServer.applySnapshot.spec` (frozen) has `srvRest E γr A` in its pre and `srvRest E γr A'` in
    its post (`EtcdServer__applySnapshot.lean:131`). It has premises `hlease` (`:73`, the image's
    lease bucket empty) and `hA'` (`:106-108`, the rest model equal to the image with `lease`
    emptied). It has **no** `lg` premise: only `applyAll.specSnap` has `γr.kv.lg = false`
    (`EtcdServer__applyAll.lean:282`).
  - Its proof's lemmas build the post's `srvRest` from `hA'`:
    - `snap_srvRest`: `unfold srvRest`, `SnapApplyRest.lean:37-50`;
    - the walk: `SnapApplyWalk.lean:140, 343-347`;
    - `SnapRecvFacts.lean:329-366`.
  - The KV side builds `leasesLive` at `L := []` (`SnapApplyKV.lean:47`,
    `SnapApplyKVLemmas.lean:119`).
  - At `E.lg = true`, the gated `srvRest E γr A'` asks for `restLeasesWith f (appliedTable A').ids …`
    and `ltHalf E (appliedTable A').ids`. With the lease bucket empty by `hA'`, that is unprovable
    unless the table is empty. None of these statements carries a fact that rules `lg = true` out.
  - `applySnapshot.spec` is not in §2's changed statements, nor in §3's table.
- *Callers affected:* `applySnapshot.wp_proof`, `snap_srvRest`, the walk, `SnapRecvFacts`'s lemma,
  and `SnapApplyKV` (the lease-free restore at `lg = false`, which must keep compiling).
- *Fix:* either of these.
  - (i) Put `srvGrantable E` (with its `lessorModeIs E.γ.leases true`) inside `srvRest`'s
    `lg = true` arm (see Q7). `applySnapshot` has `lessor.lessorRevocable E.γ.leases` in its pre
    (`:134`). `lessorPinR_agree` (`LessorLemmas.lean:118` and others) makes the two modes
    contradictory. So the proof refutes the `lg = true` arm on entry, and no frozen text changes.
  - (ii) Add `E.lg = false` to `applySnapshot.spec`'s premises. Its only caller has
    `γr.kv.lg = false` and the tie from `srvKVInvs`. List it in §3's table.

  I prefer (i): it also answers Q7.

**S-B. The send branch's own observation `mergedObs` names the exact `bkRestAt`, and
`mergedCreate_window` (proved, not a `sorry`) unfolds `srvRest` at the exact image. §2.14 gates only
`imageAt`, and calls `mergedCreate_window` a `sorry`.**

- *Principle:* "Sound/complete" (the design states every changed statement:
  `notes/spec-first-plan.md`, "Design before plumbing").
- *Evidence:*
  - `mergedObs` (`SnapSendBranch.lean:516-524`) ends in
    `bkRestAt γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) D`.
  - `mergedCreate_window` (`:535-…`) has a proof:
    - it does `iunfold srvRest` (`:613-617`);
    - it passes `(restModel … (γr.raft.pre ++ A)).bk` as the buckets' image to `srvBeSnapOk_window`
      (`:620-661`);
    - it concludes `bkRestAt_of_rb hRB hrbD` (`:687`);
    - it recloses `srvRest` (`:731-735`).

    The file has one `sorry`, at `:755`, which is `merged_image`'s.
  - `merged_image` (`:749-755`) takes `mergedObs` and gives the image certificate, through `imageAt`.
  - At `lg = true` after a grant, the observed lease bucket is not `restModel`'s. So the window cannot
    produce `mergedObs`. `merged_image`'s statement stays true but becomes unusable there.
  - "The send branch at `lg = true` reads `bkRestAtL` off `srvRest`'s `∃ f`" needs all three changed.
- *Callers affected:* `applyAll`'s send branch (`EtcdServer__applyAll.lean:375-410`,
  `ApplyAllSnap.lean:452-484`).
- *Fix:*
  - Gate `mergedObs`'s last-but-one conjunct as `imageAt`'s: `if γr.kv.lg then bkRestAtL γr.kv
    bootLog (pre ++ A) D else bkRestAt …`.
  - Restate `mergedCreate_window` with the window at the gated buckets
    `(restLeasesWith f T (restModel …)).bk` (both arms, one proof).
  - Say that `merged_image`'s `sorry` now covers the leased image too. It is still true: the observed
    ids are `kvLeases γk (pre ++ A)`, the same as `imageAt`'s `L`.
  - Add all three to §3's table (the `_false` laws by `rfl`).
  - Correct "The S2 `sorry`s (`mergedCreate_window`, `merged_image`)" to `merged_image` only.

**S-C. §2.11a's written post omits the certificate that `grantHdr` and `srvRevLb` need.**

- *Principle:* "Sound/complete"; this is the main check (is the post provable, and does it give
  what the caller uses).
- *Evidence:*
  - §2.11a's post: `… ∗ ⌜h ≠ null⌝ ∗ hdrFields h ∗ Revision h ↦ W64 (|log| − 1) ∗ ⌜2 ≤ |log| ∧
    |log| + 3 ≤ 2^63⌝`. Its glue then says "The `idxCert`/`certOk` of `grantHdr` come from `Rev`'s
    post (now kept, not dropped with `-`)".
  - `grantHdr` (§2.6) asks for `idxCert γ.idx log ∗ certOk γ log`. `EtcdServer.LeaseGrant`'s
    `srvRevLb E.γ rv` (`CompactMode.lean:57`) needs `certOk E.γ log`.
  - `certOk` (`InvStore.lean:2998`) is not derivable from `kvWriter`, which holds only `idxCert`.
    Only `Rev`'s post gives it (`store__Rev.lean`: `∃ log, idxCert ∗ certOk ∗ …`).
- *Caller affected:* the backend's `LeaseGrant`. It cannot build `grantHdr` from the post as
  written.
- *Fix:* add `∗ mvcc.certOk E.γ log` to the post. It is persistent and exact, because `log' = log`.
  `idxCert` comes from `kvWriter_cert` (`Writer.lean:43`).

### Minor

- **m1. §2.12's edit list is larger than needed.**
  - `Lease.persistTo.spec` takes `leaseBackend b …`, with `b` passed in
    (`Lease__persistTo.lean:29-38`). It never sees `lessorBackend`'s lens, so it does not change.
  - `lessor.Revoke.spec` takes `lessorBeOn` directly, not through `lessorBackend`
    (`lessor__Revoke.lean:56-60`), and already returns it. "Revoke's clause gets `Ln` back" is a
    no-op.
  - Only `Grant.spec` and `Checkpoint.spec` (`lessor__Checkpoint.lean:35`) change. Drop the other two
    from commit 2 and from §3's first row.
- **m2. `isApplyLessor_of_lessorInv`'s new premise needs `d` named.**
  - The backend contract is fixed outside the `∀ rs` lens, but `d` is existential inside the lens.
  - State the premise as `∀ d, ⌜γ.kb = some d⌝ → lessorBackend lp P f (storeWT γ)
    (lessorBeOn lp d.be) (storeRT γ) Rb`. Then `NewServer`/`SnapApplyOptsLemmas.lean:178-202`
    instantiate `lessorApplyOk`'s `RW := lessorBeOn lp d.be` (`rwLens` is reflexive).
  - Today they pass the server's write right there.
- **m3. Which list `appliedTable` is over.**
  - `appliedTable γr A := kvLeases γr.kv (γr.raft.pre ++ A)` folds from the table `[]` over
    `pre ++ A`. The KV model's own table folds from `[]` over `A` (`kvRaftSt … (log0, []) A`,
    `KVModelDefs.lean:450-457`). They agree when `pre` grants nothing.
  - §2.13's `srvRest E γr []` at `f := fun _ => 0` needs `(kvLeases γr.kv γr.raft.pre).ids = []`.
    The boot log's entries are configuration entries, so `kvTable` keeps the table.
  - State the fact and where it comes from (`pre = []` in `runSnapLgOkBody` and `applySnapshot`).
- **m4. `NewServer.specG on cmp` (`NewServer.lean`, spec `:522`) at `on = true` needs
  `lg = false` too.** §2.13 names only `specM true`.
- **m5. The auth-on arm of `applyEntryNormal` (`ApplyNormalOn.lean`) unfolds `srvRest`.** It has no
  `lg = false` fact either: that combination is excluded only at `NewServer`. Say that it uses the
  generic `srvRest_applyG`/`_snoc`, not `_false`.
- **m6. `srvGrantable`'s mode conjunct duplicates `srvSnapRO`'s.** `srvSnapRO` has
  `lessorModeIs E.γ.leases γr.kv.lg` (`SnapRO.lean:424`), and `E.lg = γr.kv.lg` comes from
  `srvKVInvs`. This is harmless. If Q7 moves `srvGrantable` into `srvRest`, keep it there: `srvRest`
  has no tie in scope.

## Q7 and Q8

- **Q7: neither of the two options. Put `srvGrantable E` in `srvRest`'s `lg = true` arm.**
  - `srvRest E γr A` is already in the pre and post of `applyEntryNormal`, `applyEntries`, `apply`,
    `applyAll` and `applySnapshot` (all five `Spec/` files name it).
  - It is already gated, and it is internal. So no frozen text changes, against three for "the pre",
    and `isServerM`'s users are untouched.
  - It is kept:
    - by `srvRest_applyG`, as a persistent frame;
    - by `NewServer`, which establishes it (§2.13 already allocates there);
    - by `srvGrantOpen`'s body, which carries it from the pre's `srvRest`. That stays true.
  - It also gives the receive proofs their refutation of the `lg = true` arm (S-A (i)).
  - `applyEntryNormal` reads `grantPermRq` off the `srvRest` it opens anyway.
- **Q8: not a question.**
  - `newHeader.spec`'s pre is `txn.kvWriter E.s E.γ log`. By definition that holds exactly
    `soleBudget log` tokens (`SoleWriter.lean:89-91`), so no caller chooses how many to lend.
  - The only state with fewer is `soleWriterOpen`, a write transaction open, which is not a
    `kvWriter`. `newHeader` is not called inside one: Txn allocates its own header.
  - So `log' = log` holds for every caller of the spec. Drop Q8, or record it as resolved by the pre.

## Go code

No bug found; nothing to file in `issues/`. Two Go facts the design rests on, noted for the trust pass:

- `quotaApplierV3.LeaseGrant` (`quota.go:54-61`) grants first and then replaces a nil error by
  `ErrNoSpace` when the quota was exceeded. Without `backendUnderQuota`, a client would be told
  "no space" for a lease that exists. The design is right to rely on that premise. The behavior is
  etcd's design (the alarm path), not a bug.
- Members store their own `minLeaseTTL`-raised TTL, and a snapshot overrides a follower's (r1's
  note). It is now harmless to the proof.

## Ranking (need of revision)

1. **S-A**: the receive proofs and `applySnapshot.spec` versus the gated `srvRest`. Fix it by Q7's
   placement.
2. **S-B**: `mergedObs`/`mergedCreate_window` ungated; `merged_image`'s role restated.
3. **S-C**: `certOk` in `newHeader`'s post.
4. m1-m6.

## Verdict

The design can be frozen once S-A, S-B and S-C are in the text. Each is a paragraph, and none
changes the design's structure:

- move `srvGrantable` into `srvRest`'s leased arm (or give `applySnapshot` an `lg = false`
  premise);
- gate `mergedObs` with `imageAt` and restate `mergedCreate_window` at the leased buckets;
- add `certOk E.γ log` to `newHeader`'s post.

Round 1's blocker is fixed. The shared image no longer names a member's TTL, and the one open
hypothesis, `srvGrantOpen`, is true of Go as far as I can check it. So `leasegrant_safe` is not
vacuous on that account.

Every other changed post I checked is provable from the callee statements on the branch:

- the grant triple from `Grant` over `RO`;
- the answer from the strengthened `newHeader`;
- `leaseGrantedAt` from the mode in `grantPermRq`;
- `srvRest_applyG` from `restLeasesWith_snoc`.

At `lg = false` every gated statement reduces by `rfl`, except the places S-A and S-B name, which
lack the fact to reduce. With those three repairs, plumbing can start at commit 1 without another
full round. A quick check of the three paragraphs is enough.
