# Review: S2–S4 "snapshots carry leases", Draft round 4 (`6d7f64326e..decf626b24`, plus `c463b6bf52`)

Read-only review of worktree `/shared/etcd-grove-leaseexp`, branch `lease-snap`. I did not build
anything. Line numbers refer to `decf626b24`. Go references are to the pinned fork in
`/shared/etcd-grove/.lake/go-src/etcd`.

## Ranking (most in need of revision first)

1. `EtcdServer.applySnapshot.specSnapM` (target 3): **BLOCKER**. With auth off, the walk cannot be
   proved from the precondition.
2. `lease.lessor.Recover.spec` (target 1): SHOULD-FIX. The statement is true of Go and the design
   is right. The docstring is stale and contradicts the statement. The scope restriction is not
   marked. One premise has no source yet.
3. The grant chain up to the client (target 4): SHOULD-FIX. The `ttl`-field conjunct is now dead.
   There is also a cluster-certificate margin and inconsistent wording of the TTL bound.
4. Removing `srvGrantOpen` (target 5): SHOULD-FIX before the Freeze, for the trust base. The
   removal itself is right.
5. Grant.spec, `leaseTTLAt_ge_req`, the lessor invariant and NewLessor (target 2): good. Only NITs.

## Go facts checked

- `Grant` (`server/lease/lessor.go:280-322`). The TTL is `max(req, le.minLeaseTTL)` (`:301-303`),
  written to the member's own backend by `persistTo`. It returns `ErrLeaseExists` only for an id in
  `leaseMap`. **A revoked id can be granted again in Go** (by an explicit `ID`).
- `Recover`/`initAndRecover` (`:600-609`, `:808-835`). It builds a fresh `leaseMap` with one new
  `*Lease` per record, `ttl = max(record TTL, this member's minLeaseTTL)` (`:817-819`). The backend
  record is not rewritten.
- `ttl` is assigned only at `lease.go:45`, `lessor.go:302` and `lessor.go:822`, so Renew,
  Checkpoint and Promote never change it. `leaseTTLAt_ge_req` is therefore true of Go: a TTL is
  `max(req, mt)` or `max(rec, mt')` with `rec ≥ req` by induction over senders.
- `EtcdServer.LeaseGrant` (`server/etcdserver/v3_server.go:434-439`) only fills in `ID` and leaves
  `TTL` unchanged. The client's `Grant` (`client/v3/lease.go:222-223`) sends `{TTL: ttl}`. So
  `Main`'s request reaching the lessor is `1`.
- `minLeaseTTL` is set at `server.go:344-349`.

No Go bug was found. Nothing new is needed in `issues/`.

---

## 1. `EtcdServer.applySnapshot.specSnapM` (`Spec/.../etcdserver/EtcdServer__applySnapshot.lean`)

**Good.**
- Replacing the empty-bucket `hlease` with `imageLeasesAt γr d.P D A'` (`:124`) is the right
  premise. It is the image's lease bucket stated the same way as `bkRestAtL` and `srvRest`'s
  leased arm. The `leasepb` decoding stays behind `MustUnsafeGetAllLeases` (`leaseRecEnc`).
  `imageLeasesAt_of_bkRestAtL` and `imageLeasesAt_nil` (`ImageLeases.lean:55,65`) are proved.
- Dropping `E.lg = false →` is right. The mode premise `lessorModeIs E.γ.leases (decide (E.lm =
  .mono))` replaces `lessorRevocable`. It is the environment's fact, which `srvSnapRO`'s `HlpM`
  already holds, and it is one spec over the mode (the hard rule "a mode is part of the state").
- In both callers `hlease` comes from `SnapImageFacts(On).hlease`. In the off path that is
  `imageLeasesAt_of_bkRestAtL` of `imageAt`'s `bkRestAtL` (`SnapRecvFacts.lean:524`).

**F1 (BLOCKER: Complete, and "every premise has a source").** With auth off, the precondition
gives no relation between the applied log `A` and the image's log `A'`, and no fact that `A'` is
committed. The only places these appear are the `on` arms:
- `snapAuthImgM .on` has `A <+: A'` (`SnapAuthRecover.lean:614`);
- `snapAuthResM .on` has `srvRLogLb γr.raft A'` (`:637`);
- the `off` arms carry neither (`:609-611`, `:636`).

The granting walk (the DRAFT `sorry` at `EtcdServer__applySnapshot.lean` proof `:136`) needs both:
- `Recover`'s ever-set premise comes from `appliedTable_granted_live`. That takes `hpre : A <+:
  A'` and the `Nodup` of the revocable grant ids of `pre ++ A'` (`ImageLeases.lean:101-104`), and
  the `Nodup` comes from `kvGrantIds` at a committed log extending `pre ++ A'`.
- The monotone premise comes from `appliedTable_mono_sub`. That needs `A <+: A'` and `plainLogM …
  .mono (pre ++ A')` (`:91-93`), which also comes from the KV invariant at a committed lower bound.
- The post `srvRest E γr A'` needs `srvEverOk E A' (U ++ ids)`, and that needs
  `srvGrantLog A ⊆ srvGrantLog A'` (`InvRest.lean:675-676`), again `A <+: A'`.

A counterexample shows the pre admits states where `Recover`'s premise is false. Take an arbitrary
`A'` whose table re-lists an id `u ∈ U` that `A` revoked. Then `u ∈ U`, `u ∉ L` and `u ∈ recs`.
So the walk's `sorry` is not just Prove work. As stated it cannot be proved, and the notes'
"(Prove: …)" label is wrong.

The auth-on/lease coupling means the granting walk happens only with auth off, so it hits exactly
the arm that lacks the facts. Both callers have them:
- `SnapImageFacts.pre : A <+: A'` (`SnapRecvFacts.lean:245`);
- `run_job_snap`'s pre carries `srvRLogLb C.ρ.raft A'`.

**Fix:** make both facts mode-free premises of `specSnapM`: `(hAA' : A <+: A')` and `srvRLogLb
γr.raft A'` in the pre. Remove them from the `on` arms of `snapAuthImgM`/`snapAuthResM` (or keep
the arms and derive them). `applyAll.specSnap(M)`'s proofs already hold both. An alternative is
the receiver's need stated as pure facts: `A <+: A'`, `(logRevGrantIds γr.kv.lm (γr.raft.pre ++
A')).Nodup`, and `γr.kv.lm = .mono → plainLogM γr.kv.cmp .mono (γr.raft.pre ++ A')`. But the lower
bound is what the callers already hold and what the KV invariant reads, so prefer it.

**F2 (SHOULD-FIX: trust base).** The `lg = false` path now goes through a DRAFT `sorry` (proof
`:141`, "the empty bucket at `lg = false`"). That path is every non-granting server's snapshot
restore. So every result that links `applySnapshot` and `applyAll`'s snapshot case now rests on a
DRAFT `sorry`. Before this change those results rested on the premise `hlease` and nothing in the
lease examples. The same is true of `ApplyAllSnap.lean:74` and `ApplyAllSnapOn.lean:84`: these are
proofs of specs every server result links, and before they had a premise, not a `sorry`.

**Fix:** prove the `lg = false` step now. It should be short: `imageLeasesAt_nil` plus "a log of
a cluster that grants none has an empty table". Before the batch goes to the user, run
`etc/tcb-report.py --check` on the collections and list in the plan which ones gain the remaining
DRAFT `sorry`s.

**F3 (NIT).** The docstring of `hA'` (`:116-118`) says the lessor's bucket is "emptied by their
`Recover`". `Recover` does not empty the lease bucket: it creates it if absent and keeps its
records. The emptying is of the rest model (`restModel_lease`). This was there before the change,
but it now reads against `hlease`. Reword to "the image's buckets with `lease` and `alarm` set to
empty are the rest model's".

**F4 (NIT, "pure premises in the precondition").** `hlease` is a new named Lean binder, not a
`⌜…⌝` conjunct. The rule says to convert a spec when you change it. The convention of this
spec's named premises (S-j1) may justify keeping it. If so, say so.

## 2. `lease.lessor.Recover.spec` (`Spec/.../lease/lessor__Recover.lean`)

**Good.**
- The ever-set premise `id ∈ U → id ∈ L` (`:69`) is the approved weakening. It is the normal case
  (a follower that applied the grant). It is exactly what `histOnce` (ids only) needs, through
  `histOnce_recover` (`LessorHist.lean:418`).
- `rq` with `rq x.1 ≤ x.2.1` (`:70`), the pre `□ [∗list] x ∈ recs, ⌜x.1 ∉ U⌝ ∨ leaseReqIs γl x.1
  (rq x.1)` (`:74`) and the post `□ [∗list] … leaseReqIs` (`:85`) are necessary, not redundant:
  - The `rq ≤ record TTL` premise is not implied by the old request for an id in `U`. `reqOk`
    bounds the request by this member's raised TTL, not by the new record's TTL, and the
    recovered TTL is `max(record, mt)`.
  - A caller-chosen `rq` is the only cluster-invariant quantity. If the lessor chose `r := record
    TTL`, a later restore from a leader with a smaller minimum would break the agreement.
- I checked the DRAFT `sorry`s' statements; all three are true:
  - `recover_hist`'s `HQx` (`LessorRecoverLemmas.lean:382`): `Un`'s ids not in `U` are not in
    `Q`, by `histIn` and `reqOk.2`.
  - `:648`: `recTTLs` gives `grantTTL mt x.2.1 ≥ x.2.1 ≥ rq`.
  - `lessor_live_perm` (`:723`): `leaseOwn`/`leaseRevokers`/`lessorAuth` are read by
    membership.
- `Lr` with `Lr.Perm (recs.map (·.1))` puts the reordering where it must be done, under `le.mu`:
  the other half of `leaseOwn` is in the lock's invariant, so a client-side law could not
  reorder. That is the smallest change.
- `U ++ recs.map (·.1)` instead of `∪` is well argued. Every use is membership, it matches
  `Grant`'s `U ++ [id]`, and it needs no lawful `BEq`.

**F5 (SHOULD-FIX: the docstring contradicts the statement).**
- `:45-47` still says "The records' ids are new to the ids the lessor ever had (`leaseEver γl U`),
  which gain them". That was the old premise, and it is now false as a description.
- `:40` says "the live set the records' ids … (`leaseOwn γl ids ∅`, `leaseRevokers γl ids`)". It is
  now `Lr`.
- The appended paragraph `:56-61` is right but sits after the stale text.

**Fix:** rewrite the summary paragraph in place:
- "the records' ids are added to the ids the lessor ever had; one it already had must be live
  (`id ∈ L`)";
- "the live set is the records' ids in the caller's order `Lr`".

**F6 (SHOULD-FIX: "no unneeded premise … a scope restriction marked as such").**
`id ∈ U → id ∈ L` is not something Go's `Recover` needs: `initAndRecover` takes any records. It
excludes a reachable Go behavior: a client re-grants a revoked id by explicit `ID`, and a follower
that applied the revoke then restores a snapshot containing the new grant. The premise exists for
the proof (`histOnce`, hence `lessorAt_absent_stays`), so it is a scope restriction. The docstring
gives only the proof reason ("so that each id stays live over an interval").

Where it is discharged. This answers the brief's "distinct grant ids":
- **Revocable mode:** by `kvGrantIds` (`InvRequest.lean:516-519`). The log's grant ids are
  generated ids masked, with no repeat, each of the prefix `kvPfx γk` (`:510`). Its source is
  `LeaseGrant.spec`'s `ID = 0` premise and `grantIdOwn`, which reaches the client as
  `etcdLeaseGrantSpecLive`'s filter `m.2 = 0` (`client/v3/InvLeaseGrant.lean:105`).
  `kvPfx` is "the one member's generator's" prefix. In a multi-member cluster, the only kind
  where a snapshot restore occurs, only the member with that prefix can propose a grant. The
  snapshot generalization inherits this restriction. It is a single-proposer scope, not stated
  anywhere near the snapshot specs. I could not tell whether the plan's multi-member adequacy
  intends this: **uncertain**.
- **Monotone mode:** no id ever leaves (`histMono`), so `U ⊆ L`. The lessor law for it
  (`histCover`, notes "Not yet applied") does not exist yet, so the premise has no source in this
  mode today.

**Fix:**
- Add a sentence to the docstring: "a scope restriction: Go recovers any records; it excludes a
  revoked id granted again (explicit `ID`), which the revocable mode's generated ids (`kvGrantIds`)
  and the monotone mode's `histMono` rule out".
- Record the single-proposer consequence in the plan's open points.

**F7 (SHOULD-FIX: "every premise has a source").** For `x.1 ∈ U`, the pre's `leaseReqIs γl x.1
(rq x.1)` has no source yet. The intended one, `srvEver` keeping `leaseReqIs u (log's request of
u)`, is listed as not applied. The notes' own observation shows its laws change at five
`applyEntryNormal` sites. "The log's request of u" is well-defined only:
- in the revocable mode, by `kvGrantIds` (one grant entry per id);
- in the monotone mode, as the first successful grant's (the table's entry), because later
  duplicate grants fail (`backendTable`'s `leaseGrantOk`, `KVModelDefs.lean:379`).

**Fix:** write `srvEver`'s new clause before the Freeze, defined mode by mode from the applied
table (`appliedTable` keeps the entry while the id is live), and check it against both modes. It
is part of the batch's surface, because it changes what every apply step carries.

**F8 (NIT: vocabulary).** The binder `rq : w64 → w64` collides with the pervasive `rq :
IRRModel` (the request) in the same chain (`grantTTLOk rq t`, `dispatch`'s `rq`). Rename it to
`req` or `reqOf`.

**F9 (NIT: "pure premises in the precondition").** The two new pure premises (`:70`) are added as
Lean implications. Convert the changed ones to `⌜…⌝` conjuncts, as the rule asks when a spec is
touched.

## 3. Grant.spec, `leaseTTLAt_ge_req`, the lessor invariant, NewLessor (target 2)

**Good.**
- `Grant.spec`'s post `leaseReqIs γl id ttl` (`lessor__Grant.lean:58`) is proved, not a `sorry`
  (`grant_hist`, `LessorLemmas.lean:417-494`). Freshness in `Q` holds in both modes:
  - revocable: `not_everIn_of_histIn`;
  - monotone: `not_everIn_of_mono` with `id ∉ L` from the success arm.
- `leaseTTLAt_ge_req` (`LessorHist.lean:566`) is true and proved. It is the smallest law `Main`
  needs: `reqOk.1` plus `ttlTie`'s domain fact. It replaces a law that is false of Go
  (`leaseTTLAt_ttl_agree`; see `nonissues/etcd-lease-ttl-differs-across-members.md`).
- `reqOk` (`InvLessor.lean:355-358`) and `histOnce` ids-only (`:335`) are well chosen. Every
  writer keeps them: `reqOk_snoc_sub` for Revoke/Attach/Detach/Checkpoint (`LessorLemmas.lean:341,
  397`), `reqOk_grant` and `reqOk_snoc_gen`.
- NewLessor's added post is ghost-only: an empty map, `reqOk` of the single empty snapshot
  trivially. An axiom review is recorded (`5463139be7`).
- `Main:324` (`leaseexpiry/Main.lean:326-333`) is a real, short proof from the client's
  `leaseReqIs … 1`.

**F10 (NIT: "name the abstraction, not where its argument comes from").** To the lessor,
`leaseReqIs γl id r` means "every TTL the history gives `id` is at least `r`, and `r` is
unique per id". After `Recover`, `r` is whatever the caller named (`rq`), which is not the
request unless the caller says so. The name states the apply layer's reading. Consider
`leaseTTLFloor γl id r`, with "the grant's request" the reading `Grant.spec`'s docstring gives.
This is optional: the name is accurate for every producer today.

**F11 (NIT).** `nonissues/etcd-lease-ttl-differs-across-members.md`'s "Proof" section still
describes option (A), "every recorded TTL ≥ the member's minimum (pending the user)". Update it to
the request bound (`leaseTTLAt_ge_req`, Q-S6 (A-ii)/Q-S8).

## 4. The grant chain carrying `leaseReqIs` (target 4)

**Good.**
- The fact travels the same path as the granted TTL (`28411daeac`):
  - `isApplyLessor`'s Grant clause (`Contracts.lean:392`);
  - `grantAnswer` (`Chain.lean:1292`);
  - `leaseGrantedResp` (`LeaseGrant.lean:66`);
  - `EtcdServer.LeaseGrant`'s proof (two lines);
  - `grantLiveG` (`v3rpc/InvLeaseGrant.lean:49`);
  - `etcdLeaseGrantSpecLive` (`client/v3/InvLeaseGrant.lean:100`).
- Each step is one frame. It is true of Go: a success answer comes only from the proposing
  member's apply of the entry, which ran `Grant`. A member that skips the entry through a restore
  times out the waiter rather than answering success.
- `grantPost`'s and `dispatch`/`Apply`'s TTL bound is the necessary source of `srvRestAt`'s and
  `bkRestAtL`'s `leaseTTLsAbove`. The lessor's contract already had `⌜ttl ≤ t⌝`, and the chain
  dropped it. This is the right fix of the first pass's false `mergedObs_of_M`.

**F12 (SHOULD-FIX: "after a change, drop what existed only for what it changed").** The
conjunct `lease.lsF "ttl" l ↦□ t ∗ ⌜req ≤ t⌝` was added (E3/R5, the same day) only for
`leaseTTLAt_ttl_agree`. That law is gone, and its one consumer now uses `leaseReqIs`:
`leaseexpiry/Main.lean:253` destructures `#Hgttl, %Hgt` and never uses them. The `*Lease`'s `ttl`
field is also implementation (an internal field of a type the client never sees), which is
against "the spec of an API".

**Fix:** drop the conjunct from the client-facing statements, keeping `leaseLiveFrom` and
`leaseReqIs`. That is `etcdLeaseGrantSpecLive`, `grantLiveG`, `leaseGrantedResp` and
`grantAnswer`. Keep `⌜ttl ≤ t⌝` and the `ttl` field in `isApplyLessor` only, where `grantPost`'s
bound consumes it. Since this is a frozen/exported change under the batching rule, add it to the
batch now. Otherwise the next round adds and removes the same text.

**F13 (NIT, "a client's certificate is the cluster's"; know the margin).** `leaseReqIs γl …` is
one member's ghost state. A client that later asks `TimeToLive` at another member cannot use it.
The request itself is a cluster fact: the log's grant entry, `appliedTable`'s `(id, ttl)`, which
`srvEver` (F7) will tie to every member's `Q`. `leaseLiveFrom γl` in the same contract already
has this one-member scope (the file header says "one member's"), so the change adds no new
limitation. Note in `etcdLeaseGrantSpecLive`'s docstring that a cluster-level form exists: the
log's request plus a per-member law `Q id = the log's request`.

**F14 (NIT: one vocabulary for one fact).** "Record TTL ≥ request" is written five ways:
- `⌜sint.Z g.ttl ≤ sint.Z t⌝` (`grantPost`, `Chain.lean:1846`; `isApplyLessor`);
- `grantTTLOk rq t` (`dispatch`, `Apply`, `Chain.lean:463`);
- `leaseTTLsAbove T f` (`srvRestAt`, `bkRestAtL`, `imageLeasesAt`);
- `sint.Z (rq x.1) ≤ sint.Z x.2.1` (`Recover`);
- `∀ p ∈ appliedTable, p.1 = x.1 → …` (`imageLeasesAt_recs`).

Use `grantTTLOk rq t` in `grantPost` too, and rename `leaseTTLsAbove` to something that says
which side is bounded (`leaseTTLsGeReq`); "above" reads ambiguously.

## 5. `imageLeasesAt` and `imageLeasesAt_recs` (`ImageLeases.lean`, `c463b6bf52` and round 4)

**F15 (SHOULD-FIX, internal lemma: state what the consumer takes).** `imageLeasesAt_recs`
(`:77-84`) gives membership equivalence of the record ids and the table ids. `Recover` takes
`Lr.Perm (recs.map (·.1))`, with `Lr := (appliedTable γr A').ids`. Getting `Perm` from `↔` needs
`Nodup` on both sides, and neither is exported:
- the record ids are `Nodup` because they are distinct bucket keys;
- the table ids are `Nodup` because of `leaseGrantOk`.

**Fix:** state `recs.map (·.1) ~ (appliedTable γr A').ids` (`List.Perm`) in place of the `↔`
clause. The bucket is `restLeasesWith`'s fold of inserts over the table's ids, read back in key
order, so the `Perm` is the natural fact. The lemma is still a DRAFT `sorry`, so changing it costs
nothing now.

## 6. Removing `srvGrantOpen`, `bootCfg`/`runCfg`'s open clause (target 5)

**Good.**
- The removal is complete: no `hslg` is left in either Main or `MainLinked`.
- `bootCfg_none`/`_mono`/`_revocable` and `runCfg_*` are simpler, and `bootCfg_ckpt`'s projection
  is updated.
- The removed obligation `runSnapLgOkBody` was stated over every apply context. It is now inside
  the proved `applyAll.specSnap(M)`, which is the hard rule "one spec per function; special cases
  are instances".

**F16 (SHOULD-FIX, same as F2).** Before, the open case was a sealed premise reaching only the
lease examples (`srvGrantOpen_open`, a single `sorry`). Now it is DRAFT `sorry`s inside proofs that
every server result links:
- `ApplyAllSnap.lean:74`;
- `ApplyAllSnapOn.lean:84`;
- `EtcdServer__applySnapshot.lean:136,141`;
- `SnapRecvOn.lean:531`.

This is acceptable for a Draft, but the plan should say so, with the `tcb-report --check` delta.
Since F1 makes `:136` unprovable as stated, fix F1 first, or the removal trades a named open case
for a `sorry` that cannot be closed.

## Summary of findings

| # | Rank | Where | Fix |
|---|---|---|---|
| F1 | BLOCKER | `EtcdServer__applySnapshot.lean:119-127` (`A'`, `hauthI`); `SnapAuthRecover.lean:609-614, 636-637` | mode-free `A <+: A'` and `srvRLogLb γr.raft A'` in `specSnapM` |
| F2/F16 | SHOULD-FIX | `EtcdServer__applySnapshot.lean` proof `:136,141`; `ApplyAllSnap.lean:74`; `ApplyAllSnapOn.lean:84`; `SnapRecvOn.lean:531` | prove the `lg = false` step now; list the collections that gain each DRAFT `sorry` |
| F5 | SHOULD-FIX | `lessor__Recover.lean:40,45-47` | rewrite the stale docstring summary |
| F6 | SHOULD-FIX | `lessor__Recover.lean:69` | mark `id ∈ U → id ∈ L` as a scope restriction (id re-grant), name its discharges (`kvGrantIds`, `histMono`/`histCover`); record the single-proposer prefix scope |
| F7 | SHOULD-FIX | `lessor__Recover.lean:74`; `InvRest.lean:675-681` | write `srvEver`'s request clause (per mode) before the Freeze |
| F12 | SHOULD-FIX | `client/v3/InvLeaseGrant.lean:103`; `v3rpc/InvLeaseGrant.lean:51`; `LeaseGrant.lean:75-76`; `Chain.lean:1298-1300` | drop the now-dead `lsF "ttl" l ↦□ t ∗ ⌜req ≤ t⌝` from the client-facing chain |
| F15 | SHOULD-FIX | `ImageLeases.lean:81` | give `List.Perm` (or both `Nodup`s) |
| F3 | NIT | `EtcdServer__applySnapshot.lean:116-118` | "emptied by their `Recover`" is wrong for `lease` |
| F4/F9 | NIT | `specSnapM` `hlease`; `Recover` `:70` | pure premises as `⌜…⌝` when touched |
| F8 | NIT | `lessor__Recover.lean:66` | rename `rq` (clashes with `rq : IRRModel`) |
| F10 | NIT | `InvLessor.lean:429` | optionally name `leaseReqIs` by what it states (a TTL floor) |
| F11 | NIT | `nonissues/etcd-lease-ttl-differs-across-members.md` | update the Proof section to (A-ii) |
| F13 | NIT | `client/v3/InvLeaseGrant.lean:87-99` | note the one-member scope of `leaseReqIs` and the cluster form |
| F14 | NIT | `Chain.lean:1846`, `KVModelDefs.lean:295` | one predicate for "TTL ≥ request"; clearer name than `leaseTTLsAbove` |

Uncertain (not verified):
- Whether the multi-member scope of the revocable mode's single-prefix `kvGrantIds` is intended
  for the snapshot results.
- The size of the trust-base change. That needs `etc/tcb-report.py`, which needs a build I was
  told not to run.
