# Review round 2: S2–S4 "snapshots carry leases" (batch items 14–26)

Read-only review of `/shared/etcd-grove-leaseexp`, branch `lease-snap`. Code reviewed:
`git diff 09425021da 768b37db8a` (notes excluded). Line numbers are at `768b37db8a`, which matches
HEAD (`1e5effa263`) for every file cited. I did not build. That the proofs check is taken from the
plan's record and from the absence of new `sorry`s in the diff. Go:
`/shared/etcd-grove/.lake/go-src/etcd`.

## Summary and ranking

No BLOCKER. Every changed statement I checked is true of Go. Every new premise of `specSnapM` has a
source at its two call sites. The five DRAFT `sorry`s are gone, and `srvGrantOpen_open` has left
the baseline and the `leaseexpiry` collection.

Targets ranked by need of revision:

1. **`lease.lessor.Recover.spec`, the ever-set disjunction (the brief's question)**: SHOULD-FIX.
   At `recs = []` the post says nothing, and a `leaseEver` handed in is lost. Exact text in Q below.
2. **`EtcdServer.applySnapshot.specSnapM`**: SHOULD-FIX.
   - `hlnil` can now be derived from the pre.
   - The `on` arms still repeat `A <+: A'` and `srvRLogLb`.
   - The docstring's list of premises is stale.
3. **`ever_live_modeM` / `lease.ever_live_mono`**: SHOULD-FIX (small). It adds a new unfold of
   `lease.lessorInv` from etcdserver; the lease package lacks the law for it.
4. **`srvRestAt`/`srvReqs`/`grantReqA`, `ImageLeases`, `histCover`, `kv_grantLog_nodup`,
   `leaseTTLsGeReq`, the grant chain**: good; NITs only.

Nothing here is a Go bug, so there is nothing for `issues/`.

## Go facts used

- `Recover` (`server/lease/lessor.go:600-609`) has one caller, `applySnapshot`
  (`server/etcdserver/server.go:1086`). Boot does not call it: it goes through `NewLessor` →
  `initAndRecover` (`lessor.go:808-835`).
- With an empty bucket, `initAndRecover` leaves an empty `leaseMap`. `leaseEver` is ghost state, so
  nothing in Go forces it to change.
- `Grant` (`lessor.go:280-322`) sets TTL = `max(req, minLeaseTTL)`. It fails with `ErrLeaseExists`
  only for an id that is live. This matches `leaseGrantOk` and `srvReqs`'s use of the table's TTL
  as the request.

---

## Q. `Recover`'s `(⌜recs = []⌝ ∨ leaseEver γl U)` pre and post (`lessor__Recover.lean:76, :87`)

**It is a defect, rated SHOULD-FIX, not a soundness or completeness failure.**

- **Principle: "No vacuous guarantee".** At `recs = []` the post's disjunction always holds through
  its left side, so the post says nothing about `leaseEver`.
- **What the pre allows.** The pre accepts `leaseEver γl U` at `recs = []`, so a caller can hand
  the resource in and never get it back.
- **What a caller must do instead.** Hold the resource back by framing, which needs a case split
  on `recs`.
- **The walk already pays this.** `SnapApplyWalk.lean:464-476` builds
  `if recs = [] then apply.everOwn E U else True` beside the disjunct just to keep it.
  `:509-518` puts it back together, including a contradiction branch for `%h : recs = []` under
  `recs ≠ []`.
- **Why no proof is broken today.** There is one caller, and it frames.

**The code returns it.** The internal lemma already gives back exactly what it took:

- `recover_hist`'s right branch (`LessorRecoverLemmas.lean:480-490`) updates the ghost variable to
  `U ++ Un` and returns `leaseEver γl (U ++ Un)`.
- Only the spec's disjunction loses the link between pre and post.

**The right post.** The disjunction is not a choice the caller should get. It is a gate on the
input, and the gate is known at the call. Make it a case split on `recs`, the same in pre and post,
so the resource is neither taken nor lost at `recs = []`:

```lean
      -- pre (replacing :76)
      (if recs = [] then iprop(True) else lease.leaseEver γl U) ∗
  ...
  {{ RET #(); ...
      -- post (replacing :87)
      (if recs = [] then iprop(True) else lease.leaseEver γl (U ++ recs.map (·.1))) ∗
```

The idiom `if … then iprop(True) else …` is already used in specs
(`Spec/k8s_io/client_go/listers/core/v1/podNamespaceLister__List.lean:44`) and in `apply.everOwn`
(`Chain.lean:746`).

**Strength.**
- It is at least as strong as today's spec for every caller. At `recs = []`, a caller that holds
  `leaseEver γl U` frames it, and `U ++ [] = U`.
- Unlike today, it cannot swallow the resource.

**The variant with no `recs` split.** A Bool `ev`:
- pre: `if ev then leaseEver γl U else ⌜recs = []⌝`;
- post: `if ev then leaseEver γl (U ++ ids) else True`.

It is equivalent under framing and adds a binder, so I would not choose it.

**Proof impact.**
- `lessor__Recover.lean:101-125`: `recover_hist` keeps its disjunctive interface. At `recs ≠ []`
  the left side of its post contradicts the records' ids being in the new snapshot.
- The walk: `:466-476` becomes a plain `by_cases` that frames `HEv0` at `recs = []` and applies
  `everOwn_of_lg` otherwise. `:509-518` loses the `(%h | H)` contradiction branch.

**Docstring.** `:47-48` becomes: "with no record, the ids' half is neither taken nor given back
(the caller keeps it; a cluster that grants none holds none)".

**Considered and not recommended now.** An unconditional `leaseEver γl U` → `leaseEver γl (U ++ ids)`.
- It needs the server to keep `leaseEver` in every mode: `apply.everOwn` ungated (`Chain.lean:745`).
- That ripples through `dispatch`/`Apply`/`grantPost`.
- It would remove both gates, so it is a candidate for later, not for this batch.

**Callers checked.** `applySnapshot`'s walk is the only `Recover` call, in Go and in the proofs.
`NewServer`/boot reach the lessor through `NewLessor`, whose post gives `leaseEver γl []`
(`NewLessor.lean:153`), and never call `Recover`.

---

## 1. `EtcdServer.applySnapshot.specSnapM` (`Spec/.../etcdserver/EtcdServer__applySnapshot.lean`)

**Good.**
- **`hAA'` (`:122`) and `srvRLogLb γr.raft A'` (`:160`) are now mode-free.**
  - This is the right repair of r1's F1.
  - Sources: `Hif.pre` (`ApplyAllSnap.lean:193`, `ApplyAllSnapOn.lean:223`) and the receive
    side's `HA'`.
  - The walk uses both: `kv_log_plain`/`kv_grantLog_nodup` at `HAlb`, `appliedTable_mono_mem`/
    `rev_mem` at `hAA'`, and `srvGrantLog_prefix hAA'` for `srvEverOk`.
- **`hlmk : E.lm = γr.kv.lm` (`:134`)** is needed in the `on` mode.
  - `srvKVInvsOn` (`KVApplyOn.lean:324-327`) says `γr.kv.lg = false` but nothing about `E`.
  - So the refutation of a granting walk under auth on (`EtcdServer__applySnapshot.lean:144`)
    needs this link.
  - Source: `srvSnapRO`'s `Hmo` at both callers.
- **`hpre0` (`:134`)** comes from `applyAll`'s `hraft` at both callers. It is consumed by
  `appliedTable_ids_granted` (proof `:269`), which `srvEverOk E A'` over the log after the prefix
  needs.
- **The granting walk.** It is one proof for both lease modes, and `Recover` is called at the
  environment's mode. This is the hard rule "a mode is part of the state", now met in the proof as
  well as in the statement.

**S1 (SHOULD-FIX, "No unneeded premise"; the brief's "redundant or derivable").**
`hlnil : E.lg = false → (appliedTable γr A').ids = []` (`:130`) now follows from the pre:

- **Off mode.** From `isServerM`, unfold `srvAtomicsM` and take `srvKVInvs`'s `kvInv` (the proof
  already does this at `:139-153`).
  - `kv_log_plain … $$ HkI HrI HAlb` gives `plainLogM γr.kv.cmp γr.kv.lm A'`.
  - `hlmk` with `AEnv.lm_of_lg_false` gives `γr.kv.lm = .none`.
  - With `hpre0`, `kvTableOf_plainM` gives the empty table. This is exactly `snapRecv_image`'s
    `hTnil` (`SnapRecvFacts.lean:582-588`).
- **On mode.** `kv_log_plain_on`/`kv_log_plainOn` (`SnapRecvOn.lean:357`) and `kvTableOf_plainOn`,
  as in `snapRecv_imageOn` (`SnapRecvOn.lean:552-553`).
- **Why the plan's reason no longer holds.** The plan kept `hlnil` as "cheaper" (round-1 fixes,
  F2) before `hpre0`/`hlmk` existed. With them, the derivation is the `lg = true` branch's first
  ten lines.
- **What dropping it removes.**
  - batch items 15 and 22 (`SnapImageFacts.hlnil`, `SnapImageFactsOn.hlnil`);
  - the `γr.kv.lg`/`E.lg` conversion at `ApplyAllSnap.lean:194`;
  - the fragility Probe 3 found: a field first stated unconditionally and false.
- **Cost.** `kvTableOf_plainOn` must move out of `SnapRecvOn` into `ImageLeases` or
  `AppliedTable`, below the proof of `applySnapshot`.
- **Fix.** Delete `hlnil` from `specSnapM`, `SnapImageFacts` and `SnapImageFactsOn`. Derive it in
  the proof's `lg = false` branch.
- **If you keep it.** The docstring must say it is a derivable premise kept by choice, and state
  both structures' fields at one gate: `E.lg`, or `γr.kv.lg`, not one of each.

**S2 (NIT, "After a change, drop what existed only for what it changed").**
- The duplicates:
  - `snapAuthImgM .on` still carries `A <+: A'` (`SnapAuthRecover.lean:614`);
  - `snapAuthResM .on` still carries `srvRLogLb γr.raft A'` (`:637`).
- Both are now premises of `specSnapM` in every mode, so callers state them twice
  (`ApplyAllSnapOn.lean:223-225` passes `Hif.pre` twice).
- Fix: drop them from the `on` arms and use `hAA'`/the pre's lower bound in the on-mode glue.

**S3 (NIT, stale docstrings).**
- `:55-56`: the list of named premises lacks `hpre0` and `hlmk`.
- `SnapAuthRecover.lean:618-619` (`snapRestImgM`) still says "with the lessor's and the alarm
  store's emptied by their `Recover`". r1's F3 fixed this wording only in the spec.
- `:131` says "DRAFT", which should go at the Freeze.

---

## 2. `SnapImageFacts`/`SnapImageFactsOn.hlnil`, `snapRecv_image` (items 15, 22)

**Good.**
- **`snapRecv_image` is now mode-generic.** It no longer takes the premise `E.lg = false`:
  - it opens and closes `srvRest` with `srvRest_open`/`srvRest_close`;
  - the lease records leave the members through `restLeasesWith_mem`;
  - the other buckets come from `bkRestAtL_other` (`SnapRecvFacts.lean:219-226`).
- The `*NL` lemmas (`:228-303`) are honest "all buckets but `lease`" versions of the plain ones.
- `restoreLogOk_kvRaftOf`'s generalization to any `lm` (`KVModelRestore.lean:280-281`) is right:
  its proof never used `.none`.
- The conditional `hlnil` (`SnapRecvFacts.lean:356`) is true; the unconditional form was false in a
  granting cluster, as Probe 3 found.
- `SnapImageFactsOn.hlnil` unconditional (`SnapRecvOn.lean:299`) is true: auth on means a cluster
  that grants none.

**Finding.** Only S1 above: if `hlnil` leaves the spec, both fields go.

---

## 3. `srvRestAt`/`srvRest` with `srvReqs`, `srvReqsIf`, `grantReqA` (item 25); `leaseTTLsGeReq`

**Good.**
- **`srvReqs E T` (`InvRest.lean:686-687`): every lease of the table at its table TTL has
  `leaseReqIs`.** True, by these steps:
  - **A grant.** It adds `(g.id, g.ttl)` only when applied, and `Grant.spec` then gives
    `leaseReqIs id ttl` at the request. Shown by `grantReqA_of_res` (`ApplyCmpArm.lean:1392`) and
    `dispatchTable_mem` (`AppliedTable.lean:254`).
  - **Revokes and non-grants.** They only shrink the table (`srvReqs_sub`).
  - **A restore.** It gives `leaseReqIs` at `tableReq (appliedTable A')` for every record
    (`Recover`'s post).
  - **Boot.** The table is empty (`srvRest_init`).
- **`srvReqs` instead of the plan's F7 per-mode clause on `srvEver`.**
  - F7 planned a clause `logReq lm L u` on `srvEver`.
  - `srvReqs` replaces it with a fact over the live table only, which is what `Recover` asks:
    `leaseReqIs` for a record whose id is in `U`, and such a record is live in `A`.
  - The mode lemmas carry it there: `appliedTable_mono_mem` in the monotone mode,
    `appliedTable_rev_mem` in the revocable mode (`EtcdServer__applySnapshot.lean:188-204`).
  - It avoids defining "the log's request" for revoked ids, which F7 found to depend on the mode.
    That is a real simplification: "a pure fact over the state before new ghost state".
- `srvReqsIf` mirrors `srvGrantIf`, the established pattern.
- `grantReqA` is persistent and vacuous off grants (`grantReqA_nonGrant`, `_noV3`), so the five
  `applyEntryNormal` sites each pay one line.
- `leaseTTLsGeReq` (`KVModelDefs.lean:297`) reads correctly. `grantPost` now uses `grantTTLOk`
  (`Chain.lean:1845`), so "TTL ≥ request" has two names, one per arity, instead of five.

**N1 (NIT).** `tableReq` (`SnapApplyPost.lean:37-39`) is `fun T id => (T.lookup id).getD 0`.
Either define it so or say why not. It lives in `SnapApplyPost` but is used by the spec's proof
and the walk; `ImageLeases` or `AppliedTable` is its natural home.

---

## 4. `ImageLeases.lean` mode lemmas (items 20, 23)

**Good.**
- Restating them over the log after the prefix is right: `appliedTable_append` already absorbs
  `γr.raft.pre`, so the lemmas need no `pre = []`.
- `appliedTable_mono_mem`/`rev_mem` (`:399`, `:419`) give each lease, not only its id. That is
  what the request step needs.
- `imageLeasesAt_recs`'s `Perm` (`:286-292`) is exactly `Recover`'s `Lr.Perm`.
- `appliedTable_granted_live`'s premise `(srvGrantLog A').Nodup` is the KV invariant's fact
  (`kv_grantLog_nodup`), not a guess.

**N2 (NIT).** The `section probe … end probe` (`:90`, `:440`) and "(S2–S4 Probe: …)" in the
docstrings (`:397`, `:417`) record the session, not the content. Rename the section, e.g. `table`.

---

## 5. `histCover`, `ever_live_mono` (`InvLessor.lean:354`, `LessorHist.lean:599`; item 24)

**Good.**
- **`histCover hs U` (every id ever had appears in the history) is true and kept.**
  - `Grant` puts its id in the new snapshot (`everIn_last`, `LessorLemmas.lean:478-483`).
  - `Recover` puts the records' ids in the recovered snapshot.
  - Every other writer leaves `U` unchanged and only appends (`histCover_snoc`).
  - `NewLessor` starts at `[]`, and its docstring is updated (`NewLessor.lean:121-122`).
- **`ever_live_mono` is true.** In the monotone mode, `histCover` with `histMono` gives that every
  id of `U` is live in the last snapshot, which is the owner's `leaseClosers`.
  - In Go, a monotone lessor never removes a lease.
  - `Recover`'s monotone premise keeps it so across restores.
- It is the law the lease package should export.

**S4 (SHOULD-FIX, "A client does not unfold the spec's definitions, or any other module's").**
- **The new unfold.** `ever_live_modeM` (`SnapApplyDefs.lean:113`) runs `iunfold lease.lessorInv`
  in etcdserver to reach `lessorRdInv`, because `ever_live_mono` is stated over `lessorRdInv`.
  This is a new cross-package unfold.
- **Precedent, not a justification.** `EtcdServer__checkLeaseTimeToLive.lean:144` does the same
  for `leaseTTLAt_ge_req`.
- **Fix.** Add to `InvLessor.lean`
  `theorem lessorInv_rdInv (lp γl) : lessorInv lp γl ⊢ lessorRdInv γl`, or state `ever_live_mono`
  over `lessorInv lp γl`, which is what the server holds. Then drop the `iunfold`.

---

## 6. `kv_grantLog_nodup` (`SnapApplyPost.lean:123-148`)

**Good.** It is true: from `kvGrantIds` with `leaseIdMask_nodup_of_pfx`, and the filtered sublist
of a `Nodup` list is `Nodup`. It is the whole-log form of `kv_entry_grantFresh`.

**N3 (NIT).** It sits in `SnapApplyPost` beside `srvKVInvsM_lg`, while its sibling
`kv_entry_grantFresh` is in `ApplyCmpArm.lean:1089` and `kvGrantIds` is in `InvRequest.lean:516`.
Put it next to `kv_entry_grantFresh`. The latter may then be derivable from it.

**Known scope, unchanged.** The revocable arm rests on `kvGrantIds`' single prefix, so only one
member can be booted in the revocable mode (the plan's own analysis after F7). The walk's
revocable arm is therefore unreachable under today's allocations. That is stated in the plan; it
is not a defect of this round.

---

## 7. The grant chain without the `ttl` conjunct (item 16)

**Good.**
- **The drop is correct.**
  - The dropped conjunct is gone from `grantAnswer` (`Chain.lean:1293-1299`), `leaseGrantedResp`
    (`LeaseGrant.lean:75`), `grantLiveG` (`v3rpc/InvLeaseGrant.lean:51-52`) and
    `etcdLeaseGrantSpecLive` (`client/v3/InvLeaseGrant.lean:103-105`).
  - Each docstring records the removal and its reason (F12).
  - `Main` and `ServedLease`'s docstring follow.
  - This weakens only an unused fact, and it removes an internal field (`*Lease.ttl`) from a
    client-facing contract, which "the spec of an API" asks for.
- `isApplyLessor` keeps `⌜ttl ≤ t⌝` as the lessor's own contract, which is right.

**On etcdstart's API (the brief's question).**
- **Where the body lives.** `etcdLeaseGrantSpecLive` is defined in client/v3
  (`Proof/go_etcd_io/etcd/client/v3/InvLeaseGrant.lean`), which has no `etc/api/` list.
- **What etcdstart shows.** It names the contract by name only, in `etcdLeaseGrantLiveAt`, in its
  importable `ServedLease` (debt group) (`interface/.../etcdstart/ServedLease.txt:79-84`).
- **The change belongs to client/v3's contract.** Batch item 16 records it there, and etcdstart's
  interface needs no change.
- **N4 (NIT).** etcdstart's committed interface cannot show this change: the meaning of
  `etcdLeaseGrantLiveAt` moved with no diff under `interface/`.
  - Add a line in item 16 that etcdstart's `etcdLeaseGrantLiveAt` changes with it.
  - When client/v3 gets an API list, its interface will carry the body.

---

## 8. `Recover.spec`, other than Q (item 19)

**Good.**
- The `reqOf` rename (F8) is applied.
- The F6 scope sentence is present (`:62-64`).
- Probe 2 showed the premises suffice; the proof uses no extra premise.

**N5 (NIT, F5 only half applied).**
- `:40` still says "the live set the records' ids with no item (`leaseOwn γl ids ∅`,
  `leaseRevokers γl ids`)". The statement gives `Lr`.
- The correction was appended at `:61-62` instead of made in place. Rewrite `:40` to "the live set
  the records' ids in the caller's order `Lr` (`leaseOwn γl Lr ∅`, `leaseRevokers γl Lr`)".
- `:63-64` should name `histCover`/`ever_live_mono` as the monotone discharge alongside
  `histMono`.

---

## Findings table

| # | Rank | Where | Fix |
|---|---|---|---|
| Q | SHOULD-FIX | `lessor__Recover.lean:76,87` (walk: `SnapApplyWalk.lean:464-476, 509-518`) | `if recs = [] then iprop(True) else leaseEver …` in pre and post |
| S1 | SHOULD-FIX | `EtcdServer__applySnapshot.lean:130`; `SnapRecvFacts.lean:356`; `SnapRecvOn.lean:299` | `hlnil` follows from `isServerM` + `srvRLogLb` + `hpre0` + `hlmk`; derive it in the `lg = false` branch, drop the premise and both fields |
| S4 | SHOULD-FIX | `SnapApplyDefs.lean:113` | lease law `lessorInv lp γl ⊢ lessorRdInv γl` (or `ever_live_mono` over `lessorInv`); no cross-package `iunfold` |
| S2 | NIT | `SnapAuthRecover.lean:614, 637` | drop the `on` arms' copies of `A <+: A'` and `srvRLogLb γr.raft A'` |
| S3 | NIT | `EtcdServer__applySnapshot.lean:55-56, 131`; `SnapAuthRecover.lean:618-619` | premise list; "DRAFT"; stale "emptied by their `Recover`" |
| N1 | NIT | `SnapApplyPost.lean:37` | `tableReq` as `(T.lookup id).getD 0`, moved next to the table lemmas |
| N2 | NIT | `ImageLeases.lean:90, 440, 397, 417` | rename `section probe`; drop session notes from docstrings |
| N3 | NIT | `SnapApplyPost.lean:123` | move `kv_grantLog_nodup` beside `kv_entry_grantFresh` |
| N4 | NIT | item 16; `interface/.../etcdstart/ServedLease.txt:84` | note that `etcdLeaseGrantLiveAt`'s meaning changes with client/v3's body |
| N5 | NIT | `lessor__Recover.lean:40, 63-64` | rewrite the live-set sentence to `Lr`; cite `histCover` |

## Uncertain (not verified)

- Whether HEAD builds. I did not build; I relied on the plan's record and on the diff having no
  `sorry`.
- The exact import cost of S1's derivation in the `on` mode: whether `kvTableOf_plainOn` can move
  below `EtcdServer__applySnapshot`'s proof without a cycle. I did not trace the import graph.
