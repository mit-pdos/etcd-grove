# Spec review: the lease-grant stage's design of the server chain (branch `lease-grant`, `5cc0eaa28a`)

Reviewer: an independent spec reviewer. Read-only: no build and no `lean-check`.

- Target: `notes/lease-grant-plan.md`, "## Design of the server chain (2026-11-02)", lines 316-638.
  Paragraphs are cited as §N.M.
- Code: line numbers are at `HEAD` of `lease-grant`.
- Go: the pin `/shared/etcd-goose-lean-wk` (`09669450f`).
- Judged by: `PRINCIPLES.md` and the examples `compaction-in-place.md`, `apply-loop-merge.md`,
  `auth-history-tie.md` and `reply-size.md`.

The main check: for each changed statement, is its post provable from the callee specs it cites, with
its pre? I read the actual callee statements, not the design's paraphrase. Most of the chain holds up.
Five places do not:

- one is false as designed (B1);
- two posts cannot be proved from the cited callees (S1, S2);
- one law's premise is too weak (S3);
- one restatement changes the `lg = false` proofs (S4).

## What is good

- **The survey (§1) is close to complete.** It finds the exact rest image (`srvRest`), the write
  right that is never lent (`E.RW` against `reqFacts`) and the snapshot-send image (`bkRestAt`).
  These are the places the plumbing tripped on. The `kvModelSt_plain` users are all refutable at
  `lg = true`. I checked the six uses: `KVLemmas.lean:518,581,708` and `ReadOn.lean:390` each open a
  client AU inside `kvInv`, so the ghost variable's validity refutes them.
- **The rest model needs no new Go facts.**
  - The `Grant` clause over `RO` reuses the lens that `revokeClause_of_lessorInv` already takes
    (`LessorDerive.lean:161-164, 260-263`). That lens gives `storeRb γ rs.bk` (= `rbPart d.γB
    (· = lease)`, `InvStore.lean:1977-1982`) and `lessorBeOn`, and gives back `RO` at any buckets
    that agree with `rs.bk` off `lease`.
  - `lease.lessor.Grant.spec`'s put, `rbSet rb leaseName (u64Le id).reverse (leaseEnc id (grantTTL mt
    ttl) 0)` (`Spec/.../lessor__Grant.lean:52`), is `(restGrant mt id ttl rs).bk` (`grant_bk`,
    `RestLease.lean`).
  - `restAfter` of a grant is the identity (`RestModel.lean:111-117`). `GMap` has extensionality
    (`Perennial/Std/GMap.lean:31`), so `restEntry` and `restGrant` commute as values.
- **The quota argument is right.** `quotaApplierV3.LeaseGrant` (`apply/quota.go:54-61`) sets
  `ErrNoSpace` only when `!Available`. `apply.backendUnderQuota` (`Contracts.lean:630-641`) makes
  `Available` true, and `quotaReqTy` already lists `*LeaseGrantRequest` (`:625-628`).
- **The dispatch facts are checked against Go.**
  - A grant is dispatched only with `shouldApplyV3` (`uber_applier.go:126-148`).
  - `authApplierV3` does not override `LeaseGrant` (`apply/auth.go`: no such method).
  - `needAdminPermission` is false for a grant.
  - The backend answers a non-nil `*LeaseGrantResponse` even on error (`apply/backend.go:83-92`).
    `raftRequest` drops it on `result.Err` (`v3_server.go:1019-1021`).
  - `WarnOfExpensiveRequest` constrains no response (`Spec/.../txn/WarnOfExpensiveRequest.lean`).
- **(C) keeps every KV text.** It answers the user's (c) with no new premise on the frozen KV specs.
  The two results the example needs do not rest on any KV client update:
  - `EtcdServer.LeaseGrant.spec`'s pre: `isServerReq`, the reader, `E.RD`, `idCred`, the context,
    `leaseGrantReqOwn`.
  - `EtcdServer.LeaseLeases`, which reads `s.lessor.Leases()` directly (`v3_server.go:737-749`).
  - `etcdReached` comes from the store's certificate (`ClientModel.lean:393`), not from `etcdKV`.
- **The gating discipline (§0 notation) is the one `compaction-in-place.md` asks for.** Most of §2
  meets it: `rqOk`, `reqPropOk`, `kvInv`, `srvRest`, `ltHalf`, `leasesLive`. S4 and S5 are the
  exceptions.

## Findings

### Blockers

**B1. The rest image uses a member's `minLeaseTTL` (`E.mt`), but a snapshot image is shared by the
cluster. So `srvGrantOpen` (`runSnapLgOkBody`) is false in a cluster whose members differ in
`minLeaseTTL`, and §2.14's `bkRestAt c0 mt …` has no `mt` to take.**

- *Principles:* "Sound" (the design's own line 327: "no false statement behind a hypothesis"); "A
  client's certificate is the cluster's"; "A configuration premise is no stricter than what the Go
  code accepts".
- *Evidence:*
  - Go sets `MinLeaseTTL: ceil((3*ElectionTicks/2)*heartbeat)` per member, from its own `cfg`
    (`server/etcdserver/server.go:344-349`). `lessor.Grant` stores `l.ttl = max(ttl, minLeaseTTL)`
    (`lessor.go:301-303`), and `persistTo` writes that TTL (`lease.go:55-61`). So two members applying
    the same grant can write different records, and a follower that receives a snapshot gets the
    leader's records.
  - §2.9 makes the apply thread's image `E.RO (restLeases E.mt …)`, with `E.mt` the member's
    (§2.13: "choose `E.mt` from `lessorCfg`").
  - `runSnapLgOkBody` (`InvRun.lean:443-479`) quantifies over every apply context `C` and promises
    `applyRes C A'` (that image) after installing a received snapshot. Its docstring says it covers
    multi-member clusters.
  - For a TTL below the larger of two members' minima, the received bucket is not
    `restLeases C.E.mt …`. So the triple is false, and the `sorry` `srvGrantOpen_open` that discharges
    it is a false statement under `leasegrant_safe`.
  - Independently, §2.14's `bkRestAt c0 mt bootLog L D` sits in `imageAt` (`InvImage.lean:91-95`),
    which the snapshot certificates and `snapDirInv` use cluster-wide. No member's `E.mt` can go
    there.
- *Callers affected:* `srvGrantOpen_open` → `leasegrant_safe`; `SnapSendBranch`;
  `SnapRecvFacts`/`KVModelRestore` (users of `imageAt`).
- *Fix (preferred):* keep the stored TTL out of the shared image.
  - At `lg = true`, `srvRest` and `bkRestAt` state "for each id of the table, the bucket holds
    `leaseEnc id t 0` for some `t`". Write it as an existential `f : w64 → w64` with
    `restLeasesWith f table`.
  - The `Grant` clause keeps its exact member-local post `RO (restGrant E.mt id ttl rs)`, and
    `srvRest_applyG` extends `f` at `id`.
  - Nothing needs `t`: the example reads only ids.
- *Fix (rejected):* `KVNames.mt` with a `NewServer` premise `minLeaseTTL = γk.mt`. That is a
  configuration premise stricter than Go.

### Should fix

**S1. §2.11: the backend triple's `grantAnswer … log` (`appliedHdr log` with `Revision ↦□ rv`,
`sint.Z rv = |log| − 1`, `rv ≠ 0`) cannot be proved from the callee it cites, `newHeader`.**

- *Principle:* "Sound/complete" (the design must state every changed statement, `notes/spec-first-plan.md`,
  "Design before plumbing").
- *Evidence:*
  - `apply.applierV3backend.newHeader.spec` (`Spec/.../apply/applierV3backend__newHeader.lean`)
    returns only `⌜h ≠ null⌝`. It gives no field ownership, no `Revision` value and no bound.
  - §2.11 claims "(the KV's `Rev()` at the sole writer: `rv = |log| - 1`)" and "`appliedHdr` as
    `Put`'s". But `Put`'s header is allocated by the txn package, not by `newHeader`.
  - The grant arm of `rqOk` is `grantKindOk` (`Chain.lean:253-256, 278-280`). Unlike `putOk`
    (`:234`), it carries no `log.length + 4 ≤ 2^63`, so the triple's pre has no source for
    `appliedHdr`'s bound.
  - The bound is available elsewhere: `mvcc.store.Rev.spec` gives `log.length + m + 3 ≤ 2^63`,
    `idxCert`, `certOk` and `v = |log| − 1`.
- *Callers affected:* `EtcdServer.LeaseGrant` (§2.5.3: `rv ≠ 0`, `srvRevLb`, `respHdrOwn`).
- *Fix:* add `newHeader.spec` to §2 as a changed statement, with its post strengthened:
  - the fresh header owned (`respHdrOwn`-shaped);
  - `Revision ↦ W64 (|log| − 1)`;
  - `|log| + 4 ≤ 2^63` and `2 ≤ |log|`, from `store.Rev` at `kvWriter`'s log and `log0 = [[],[]]`.

  Strengthening a post is compatible for its 37 using files. Alternatively, put `putOk log` into the
  grant arm of `rqOk` and say where the apply thread proves it.

**S2. §2.11/§2.6: `grantAnswer` promises `∃ i, leaseGrantedAt γl i g.id`, but the cited `Grant`
clause gives `leaseLiveFrom γl 0 id l`. The conversion needs `lessorModeIs γl true`, which the
triple does not have.**

- *Evidence:*
  - The `Grant` clause's post is `Contracts.lean:376-381`.
  - `leaseGrantedAt` contains `lessorModeIs γl true` (`InvLessor.lean:453-454`), and
    `leaseGrantedAt_of_live` takes it (`:488-490`).
  - The mode is held only in `srvSnapRO` (`SnapRO.lean:424`). The triple's pre (§2.11) and
    `grantPermRq` (§2.10) do not name it.
- *Fix:* put the mode in `srvGrantable`, as `□ (⌜E.lg⌝ → (∀ id, leaseGranted …) ∗
  lessorModeIs E.γ.leases true)`, and in `grantPermRq`. Or let `grantAnswer` carry the mode-free
  `leaseLiveFrom` and convert in `applyEntryNormal`, which has `srvSnapRO`.

**S3. §2.9: `srvRest_applyG` "replaces `srvRest_apply`'s `plainCover` premise by `rqOk E.lg`".
`rqOk` is too weak for that.**

- *Evidence:*
  - `restOut` of a skipped or rejected outcome is the identity (`InvUber.lean:156-158`).
  - `restEntry` always applies `restAfter` (`InvRest.lean:243-251`). `srvRest_apply` needs
    `plainCover` exactly to exclude `noSideEffect`/`needAdminPermission` (`InvRest.lean:341-355`).
  - `rqOk`'s `clusterVersionSet` arm checks only the semver (`Chain.lean:287`).
- *Fix:* take the premise `plainCover rq ∨ grantPropOk E.lg rq` (what `plainEntryM` gives,
  `KVModelDefs.lean:177-179`). `grantKindOk` already rules out `noSideEffect` and admin.

**S4 (question 4). §2.14 restates `bkRestAt` ungated. At `lg = false` its old meaning is then only a
law under a plain-log premise, which the snapshot-receive proofs must now obtain.**

- *Evidence:*
  - `bkRestAt_boot` (`InvImage.lean:187-197`) derives "lease bucket empty" (the walk's `hlease`)
    from `bkRestAt` alone, today with no premise.
  - With `restLeases (kvTableOf …)` inside, it needs `kvTableOf … L = []`. That holds only for plain
    `L`, which `SnapRecvFacts.lean` and `KVModelRestore.lean` do not carry.
  - This is a re-proof at `lg = false`, against the design's notation paragraph and
    `compaction-in-place.md`.
- *Fix:* gate `bkRestAt` on `γk.lg` inside `imageAt`, which already takes `γk`. Combine this with
  B1's shape. Also restate §2.14 against the real definition: it is per bucket, `∀ n ∈ restBuckets,
  D.lookup n = bkRestOf …` (`InvImage.lean:83-85`), not `rbData D = ….bk`.

**S5 (question 4). "`lg = false` means what it means on `lean`" is claimed for the whole chain, but
several changed statements are not gated.** Each is harmless, because its new part is reached only
through a grant, which `rqOk false` excludes. But the design should list them, with the law each
caller uses, rather than claim reduction:

- `isApplyLessor`'s `Grant` clause (`RW` → `RO rs`, a new `mt` argument at all `lg`);
- the four `LeaseGrant.spec`s;
- `appliedOkM`/`resPostM`/`resultIsW` (a new conjunct for grant kinds at any `lg`);
- `dispatch.spec`/`Apply.spec` (`+ grantPermRq`, `+ ltHalf`: the `lg = false` callers need
  `grantPermRq_of_rqOk_false` and `ltHalf_false`);
- `kvInv`'s ≈10 openers. They are generic in `γk.lg`, not "off mode" (§3), so each needs a case split
  or a fraction-generic argument (`kv_revLbZ_le` works at any fraction; `kv_prop_auW` splits).

### Minor

- **M1. Trust-base labels (question 3).**
  - Of the "trusted" statements in §2.15, only `lessorApplyOk` is trusted. It is `lease.NewLessor`'s
    post (`Spec/.../NewLessor.lean:135`), so the `axiom` skill reviews the `NewLessor` axiom.
  - `isApplyLessor` is derived (`LessorDerive.lean:246`), and `bkRestAt` is internal.
  - The restatement is true of Go. `RW` lends only the lessor's half of `le.b`; `persistTo(le.b)`
    reads the field before `BatchTx()`, and `LockInsideApply`/`Unlock` never touch it
    (`lease.go:55-61`).
  - It gives back what it took (`RW`) and still spends the counted `wbTok`.
  - Write out its text for the axiom pass. The design does not say which of `lessorBackend`'s `T`/`R`
    the lent part moves to. The lens `□ (T -∗ lF "b" …)` (`LessorBackend.lean:122-125`) must still
    reach `le.b`. And `Grant.spec` must return it on the error arm too, which drops `T` today.
- **M2. "Local".** §2.9 puts `srvGrantable` into `srvKVInvs`, an aggregate with 167 uses that every
  stage adds to. The apply thread is its only user. Put it beside `lessorModeIs` in `srvSnapRO`, or
  only in `grantPermRq`'s supplier.
- **M3. Mode-indexed siblings.** These could each be the one lemma, parametric in `lg`:
  - `srvClusterBootG_alloc`/`alloc1G` beside `srvClusterBoot_alloc`/`alloc1` (§2.3), returning
    `if lg then True else etcdKV …`.
  - `kv_lease_grant_served` beside `kv_lease_served` (§2.2), which also gives `etcdLeaseGrantAt`
    under `srvGrantsLeases`.

  Dropping `etcdKVAt` is not needed for soundness: the contracts stay true, vacuously, under (C).
- **M4. `dispatchIds` ignores the outcome.** It is exact only because `grantKindOk` forces
  `.dispatched`. Writing it over `out`, as `restOut` is, removes that side argument.
- **M5. Not checked.** I did not check every Range path's refutation under (C). In particular, a
  serializable read that fires its AU at the local store would need `kvInv` open at the firing.

## The open questions

- **Q1. (C): agree.** It is the smallest realization of (c), and at `lg = true` nothing the example
  needs rests on a client AU (checked above). Two caveats:
  - Under "No vacuous guarantee", every KV result is vacuous in a granting cluster. Say so in the
    docstrings of `kvInv` and of `NewServer.spec`'s `%Hslg` row, and in `leasegrant_safe`'s.
  - (A) would make four frozen KV specs gain a premise. (B) undoes L3a.
- **Q2. (ii): agree.** It follows the `authnArM`/`authnAnsM` precedent (`ReqOn.lean:110-131,
  280-330`) at about 15 sites instead of about 184. Fix S2 in it.
- **Q3. (a): agree.** One variant is worth a look: put the live set in `RestM` (`rs.lids`), with
  `ltHalf` inside the server's `RO`. Then `Apply.spec`/`dispatch.spec` need no new `∀ T`/`ltHalf`
  argument. The frozen texts change less, and the backend triple reads `T` from `rs`. Cost: the RO
  lens must expose the half.
- **Q4. (a): agree.** See M1. (b) breaks the exact image.
- **Q5. (a), with B1's TTL abstraction and S4's gate.** (b) re-meets the circularity of commit 1.
- **Q6. Require `lg = false` with auth on: agree.** The guard is `False` there
  (`srvGrantGuard_false`, `InvApplier.lean:494`), and no example needs it.

## Go code

No bug found. Nothing to file in `issues/`.

One upstream behavior was found, of note for B1: members with different `ElectionTicks`/`TickMs`
store different TTLs for the same lease, because each applies its own minimum. A snapshot replaces a
follower's with the leader's. This is etcd's design, it is not a panic, and the corruption checker
hashes only the key bucket. I found nothing on it in `issues/`.

## Ranking

1. **B1** (`mt` in a cluster-wide image; `srvGrantOpen` false as designed).
2. **S1** (`newHeader.spec` missing from the chain; rv and bounds unprovable).
3. **S2** (the mode for `leaseGrantedAt`).
4. **S4** (`bkRestAt` gate).
5. **S3** (`srvRest_applyG` premise).
6. **S5** (list the ungated statements).
7. M1-M5.

## Verdict

The design is not ready to freeze; it needs one more short round, not a redesign. Its structure is
sound and should be kept: (C), the tie by halves, `Grant` over `RO`, the answer beside
`dispatchAnswer`, and the gated `srvRest`. Most of the glue is provable from the callee statements as
they stand on the branch. But B1 makes the one hypothesis left open (`srvGrantOpen`) false in a
cluster whose members have different minimum TTLs, and leaves §2.14 with no `mt` to name. S1 and S2
are posts that the cited callees do not give. All of these are fixes of a paragraph each:

- abstract the stored TTL in the shared image;
- add the strengthened `newHeader.spec`;
- put the mode in `grantPermRq`;
- gate `bkRestAt`;
- tighten `srvRest_applyG`'s premise.

Once they are in the text, a quick re-check of §2.9-§2.14 should be enough to freeze and plumb.
