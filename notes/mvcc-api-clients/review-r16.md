# Review of mvcc's API, round 16 (before the freeze)

2026-11-03. Read-only review of branch `mvcc-api` at `53ee8abb64`. It concentrates on
`git diff b01d7bada3 HEAD -- Spec/go_etcd_io/etcd/server/v3/storage/mvcc/`. Paths are relative to the
worktree unless absolute. Nothing was built or edited.

## Verdict

**One finding blocks the freeze (F1).** `mvccImage_snapshot.law` cannot be proved from
`backend.Snapshot.spec`, its stated premise, once a compaction key has been written to the backend
after it was opened. Every `Compact` writes one, and so does a `Restore` that resumes a compaction.
Fixing it changes a statement: the backend's Snapshot axiom, or the law's premise. That decision
belongs to the user, before the freeze.

**One finding needs internal ghost state that the frozen invariants note does not have (F2).** The
law is provable as stated in the non-compacting case. But its proof needs an exclusion device under
the whole `mvccBackend` share. A small spec addition (`isMvcc` in the law's precondition) would keep
`mvccBackend`'s definition from absorbing the store's invariants.

**F3 is a one-word fix.** `mvccImage_fresh.law` needs `|==>`.

The rest are low-severity minimality or documentation items.

I checked the notify-step receipts, Restore's dropped length bound, the lease-delete law's `End`
triple and `reach_logWf.law`. All of them are provable from the code and the invariants as they
stand.

I found no Go bug.

---

## Findings, ranked

### F1 (blocking): `mvccImage_snapshot.law` is unprovable for a store that has compacted on its backend

**Statement.** `Api.lean:941-959`:
- the post gives `∃ σ u, Φ σ ∗ mvccImage D σ.log σ.crev u`;
- the law's only source of facts about `D` is `backend.backend.Snapshot.spec`
  (`Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`).

**Why it fails.** `mvccImage`'s obligations (`Api.lean:201-211`) concern `D`'s compaction keys:
- `u` holds iff `scheduledCompactRev > finishedCompactRev`;
- when `u` holds, `c` is the scheduled revision;
- `L`'s last revision is the largest of the Key bucket's last revision and the two compaction
  revisions.

`backend.Snapshot`'s post states nothing about those two keys after they have been written:
- **The observation `Q` does not see them.** It is over `sData P D`, `hkData P D` and `rbData P D`.
  For the store's backend (`KBReal.P`, `Proof/.../mvcc/InvStore.lean:110-115`):
  - `HB := (· ≠ keyName)`, so `sData`/`vData` cover the Key bucket only (`Model2.lean:176-184`);
  - `HK` holds only the consistent-index and term keys;
  - `RB` holds only `restBuckets`.

  The compaction keys (`fkKey`, `Model2.lean:411`: `meta`/`scheduledCompactRev`,
  `finishedCompactRev`) fall in none of the three.
- **`fkRd` gives their values only before any write.** The remaining fact is
  `fkRd γ P (D, ⟨∅, 0⟩)`, whose `fkOkRvG` (`Model2.lean:504-505`) gives the values
  (`fkValRv … g.2.2`) only while the reader's flag bound is at most the value it had at the open.
  A put of a compaction key raises the flag (`fkPut`, `InvBackend.lean:427ff`, and the docstring of
  `fkOkG`). After that, only `fkOk`'s well-formedness bit remains.
- **The store's own record is not tied to `D`.** `compactRes`'s `metaCompact γ 1 sched fin`
  (`InvStore.lean:2667-2671`, `:2709`) is "its own view", a ghost variable of mvcc only.

So once the store has written a compaction key since the backend was opened, the backend's spec
gives the law no way to learn `D`'s values.

**Failing scenario.** A compacting etcd cluster (`compactkv`, or etcd itself):
1. The leader applies `Compact(5)`.
2. `store.updateCompactRev` calls `SetScheduledCompact` (`Code/.../storage/mvcc.lean:2982`, inside
   `store.updateCompactRev.impl`, `:2941`), which puts `scheduledCompactRev`. Later the job puts
   `finishedCompactRev` (`:4419`).
3. A follower falls behind, and the leader's apply thread runs `createMergedSnapshotMessage`, whose
   `s.be.Snapshot()` is where the server's `senderImage.law` applies this law.
4. The proof must show that `D` holds `scheduledCompactRev = 5`. The premise does not give it.

Also, on the receiving side a `Restore` with `u` calls `compactLockfree`, which goes through
`updateCompactRev` and writes the key again. Every member that ever compacted is affected.

**Today's proof never covered this case.** The sender's key observation (`txn/KeyObs.lean`,
`kvWriter_keyObs`, `kvWriter_noCmp`, `writerPin_noCmp`) is exact only for `d.cm = false`. It rules
the compaction keys out by the no-compaction token (`fkRd_abs`). Round 16 generalizes the sender to
compacting stores without the backend fact that generalization needs.

**Callers affected:**
- the server's G3 (`ServerSpecs.lean` §3c: `senderImage.law`, `dbImageA_of_send`, hence
  `dbImageA_open.law` and `restoreArgs.law` on the receiver);
- every compacting example's adequacy proof through the snapshot path.

The server draft's "No obstacle found" (`clients-server.md`, (b), "The interleaving checked") is
wrong in the compacting case.

**Minimal fix.** Give the observation the compaction keys' committed values, tracked by the backend
the way it tracks the hook's own keys. The new backend predicate `fkdOwn γ v` is half the batch lock's
and half the client's (mvcc keeps its half in `compactRes`, beside `metaCompact`, and the two agree).
`UnsafePut` at a compaction key takes the client's half and updates both halves (`fkPut` gains it).
The Snapshot spec's `Q` takes the values:

```lean
abbrev backend.backend.Snapshot.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp) (R : IProp GF)
    (Q : VData → GMap (GoString × GoString) GoString → GMap GoString BktData → FkVals → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ R ∗
      □ (∀ (vd : VData) (d : GMap (GoString × GoString) GoString) (r : GMap GoString BktData)
          (v : FkVals),
        R -∗ W -∗ Pk -∗ viewAt γ vd -∗ hkOwn γ d -∗ rbOwn γ r -∗ fkdAt γ v -∗ ⌜Q vd d r v⌝) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : Data), RET #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp);
      snapOpen sp D ∗ bOpen γ qo ∗ R ∗ fkRd γ P (D, ⟨∅, W64 0⟩) ∗
      ⌜Q (sData P D) (hkData P D) (rbData P D) (fkVals D)⌝ }}
```

Here `fkdAt γ v` is the batch lock's half at the committed values `v`. `mvccImage_snapshot.law` keeps
its statement; its premise is this spec.

This strengthens a trust-boundary axiom. It is the user's decision ("strengthen the axioms in place
… put it to the user", `PRINCIPLES.md`, "One spec per function"), and it changes a proved backend
spec (`UnsafePut`'s `fkPut`).

**Alternative fix** (the principle's split): keep `backend.Snapshot.spec`, and add a separate
`backend.backend.SnapshotFk.spec` with the post plus the compaction-key fact. Only the law takes it,
so only the snapshot-sending results rest on the stronger claim.

**Not acceptable:** gating the law on a non-compacting store. The API has no compaction mode, and a
gate would split every proof above it.

### F2 (medium; spec provable, invariants note incomplete): the law's proof needs an exclusion device the note does not have

**What the proof must do.** The law's proof commits the client's update before the call (the only
option: the observation passed to `backend.Snapshot` is a plain persistent wand to a pure fact, so it
can open neither an AU nor an invariant). It fixes the pure `Q'` from the peeked `σ`. At each commit
inside the call, from `R' ∗ W ∗ …` alone, it must then show:
- the batch lock's log `L_w` (`writerRes`'s `Hwv : ghostVar γ.wv ½ L`, `InvStore.lean:2895-2902`)
  is `σ.log`;
- every deletable key's compaction revision (`storeDlReg`/`delKeyI`'s `crevLb c`,
  `InvStore.lean:2430-2444`) is at most `σ.crev`.

**Why the frozen note's definitions cannot do it:**
- **The share excludes nothing.** `mvccBackend γ q` is "a fraction `q` of the writer's fragment
  (`writerFrag`/`curAt`)" (`notes/mvcc-api-invariants.md` §2). That is a `dghostVar` fraction
  (`InvStore.lean:450`, `:498`) whose other parts sit in `fieldShare`, `revMuBody`, `writerInv` and
  `readerPool`. The full share plus an `End`'s share `q` is still a valid fraction, so the whole
  share does not exclude a concurrent `End`.
- **The full-share holder cannot reach the other half of `γ.wv`.** That half is in `writerL`, which
  `writerInvBody` (`InvStore.lean:3230-3235`) releases only to a holder of `writerKey`, which comes
  from the batch lock.
- **An open write transaction can coexist with the whole share.** `Write` returns its share while the
  transaction holds `writerL` (`Api.lean:296-297`).

**What the internals must gain** (internal only):
1. `mvccBackend γ q` carries a genuine fractional token of total `1`. `End`, `Put`, `DeleteRange`,
   `Compact` and `Restore` hold their share across the step that changes the state.
2. `writerInvBody` gains a frozen state, which the full-share holder enters and leaves:
   - it deposits the whole token and takes a half of a ghost value paired with `W`'s `γ.wv` half;
   - the half also carries a `crevUB` part at `σ.crev`;
   - a writer that finds the frozen state derives a contradiction from its own share.
3. The open-transaction case: the holder takes the deposited `writerKey`, so every commit's `W`
   contradicts it and the observation is vacuous. The commit cannot happen anyway, since the
   transaction cannot `End`.
4. `mvccBackend` carries `isBackend B.γB B.P (mvccW gx) Pk B.b` and the store's invariants
   (`writerInv`), because the law's precondition has no `isMvcc`.

**Spec-side mitigation (recommended now; free for the server, whose `kvStoreInv` holds `isMvcc`):**

```lean
  ∀ (kv : GoInterface) (γ : MvccName) …,
  {{ … ∗ isMvcc kv γ ∗ mvccBackend γ 1 B Pk ∗ … }} … {{ … }}
```

**Optional.** With the token of item 1, the impl can prove `pending = none` at the commit. The update
can then take `Write`'s begin shape (`AU <{∃∃ σ, mvccState γ σ}> <{⌜σ.pending = none⌝ ∗ mvccState γ
σ, COMM Φ σ}>`), the closest sibling's. The server's `auBegin` builder then serves for it, and
`kvAus.law`'s new third conjunct (`auSnap`) goes. Proving `pending = none` costs the impl an
invariant fact: "`pending = some` → a share is lent to an `End`".

### F3 (medium-low; provability): `mvccImage_fresh.law` needs an update modality

**Statement.** `Api.lean:825-829`: `⊢ mvccImage D mvccStart.log mvccStart.crev false`.

**Why.** The note defines `mvccImage` as the image facts ∗ `⧖ (logCh L)` (§4.3). At `[[],[]]` that is
`⧖ 0`, which Perennial gives only under a bupd: `preceipt_zero : ⊢ |==> preceipt 0`
(`.lake/packages/perennial/Perennial/GooseLang/Receipts.lean:203`, a `monoNatLbOwn_0` allocation).
The law is provable only with a contorted definition, such as `⌜logCh L = 0⌝ ∨ ⧖ (logCh L)`.

**Caller.** The server's boot (step 4) runs inside a fupd, so the fix costs it nothing.

**Fix:**

```lean
abbrev mvccImage_fresh.law : Prop :=
  ∀ D : backend.Data, (∀ k, backend.dget D mvcc.keyName k = none) →
    backend.dget D schema.metaName mvcc.schedKeyBytes = none →
    backend.dget D schema.metaName mvcc.finKeyBytes = none →
    ⊢ |==> mvccImage (GF := GF) D mvccStart.log mvccStart.crev false
```

**The premises are right.** `NewStore`'s `restore` over a Key bucket with no entries and no
compaction keys yields `currentRev = 1` (the initial value), `compactMainRev = -1` and no resumed
compaction. That is `[[],[]]`, `-1`, `false`. A fresh bbolt file (`bootOk`'s empty data) meets the
premises trivially.

### F4 (low-medium; minimality, locality of a size assumption): `keySized` is now derivable and could leave `mvccBackendFor_open`

**Statement.** `Api.lean:817`: `□ (∀ γ b', keySized γ P b') ∗ …`.

**Where it flows.** It is threaded from the server's boot contract (`etcdserver/InvBoot.lean:407`,
"no bbolt file holds `2 ^ 62` keys") into the exported results (`etcdserver/Results.lean:838`,
`:916`, `:1071`, `SnapRO.lean:423`). Its stated reason (`BackendBridge.lean:594-600`) is that
"nothing bounds a bucket's size … the store's log". Round 16 removed that reason:
- every Key-bucket entry is a revision of one of `L`'s changes;
- the read buffer's entries are the writer's pending changes;
- so a reader state's Key entries number at most `2 · logCh L`, which is below
  `2 · receiptBound ≤ 2 ^ 49 < 2 ^ 62`.

**Cost of keeping it.** It is the brief's "size assumption less local than it could be".

**Fix.** Drop the premise. The store's range proof derives `keySized` from its bucket view and the
receipts. The internal proof cost is uncertain: the bridge's range lemmas take it per reader state.
Dropping it is cheap before the freeze and not forced after it (keeping it is sound), so treat it as
minimality, not a blocker.

### F5 (low; invariants note stale or incomplete for round 16)

- **A stale Restore row.** §3's `Restore` row says "the budget re-based at `σ'.log.length`"
  (`notes/mvcc-api-invariants.md:108`). That contradicts §4.3: no relative budget, and the receipt
  comes from `mvccBackendFor`.
- **Laws missing from §5.** Its list of laws to prove lacks `mvccImage_fresh`, `mvccImage_snapshot`,
  `reach_logWf`, `mvccTxn_leaseDelete`, `wsSentLb_zero` and `names_nonempty`.
- **Definitions missing from §2.** `mvccImage` and `mvccBackendFor` are not defined there (only §4.3
  mentions them). Nor does §2 have F2's device.
- **Restore's length bound.** It follows from `MvccReachable σ'` (committed revisions after the first
  two are non-empty: `commitLog`, `InvStore.lean:5666`) and `⧖ (logCh σ'.log)` (`preceipt_lt`). That
  also needs `receiptBound ≤ 2 ^ 48`, a premise of `New` only. Say that `isMvcc` records it.
- **Event positivity.** `wsRecvOk`'s new positivity conjunct (`ApiState.lean:174-175`) must be
  recorded per received response, unconditionally: not inside §2's `onceUpTo →` implication, since
  events after a lossy compaction must still be positive. Its sources:
  - at the send: the index's version facts;
  - for deletes: `watchableStoreTxnWrite.End` sets `ModRevision = rev` and `kvsToEvents` patches
    tombstones.

### F6 (low; minimality): positivity has no consumer in the drafts

- **`wsRecvOk`'s event positivity.** The watch draft says per-result facts "do not suffice" and takes
  `LogSmall` from `histLb`'s receipt (`clients-watch.md`, round-16 update §1). The tester
  (`examples/mvccrand/mvccrand.go:703-726`) checks events by equality with its model.
- **`kvSortOk`'s strictness.** txn uses only `kvSortOk_nonneg` (`clients-txn.md` §2). The server's
  S5 was about non-negative versions, which `stateOk` closes.

Both are true and cheap, so keeping them is defensible ("generally useful"). But `kvSortOk`'s
docstring claims a consumer ("client/v3's `0 < version`") that gets the fact elsewhere. Either name
the real consumer or soften the docstring.

### F7 (low; shape)

- **`reach_logWf.law`** (`Api.lean:919-920`) is a fact about `ApiState`'s own definitions: prove it
  once in `ApiState` as a theorem, not as an implementation obligation.
- **One form for the receipts.** The five receipts are all `⧖ (logCh σnew.notifiedLog)`, but they
  are written in three forms:
  - `σ.log ++ [pend]` (End and the lease-delete law);
  - `σ.log ++ [[.put …]]` (Put) and `σ.log ++ [ds σ]` (DeleteRange);
  - `σ'.log` (Restore).

  Export the two rewrites every client keeping `⧖ (logCh σ.notifiedLog)` needs:
  `(σ.notify p).notifiedLog = σ.log ++ [p]` when `p ≠ []` and `σ.pending = none`, and
  `logCh (L ++ [[]]) = logCh L`. The server draft uses the second unproved.
- **`mvccState_reachable`'s `length + 3 ≤ 2 ^ 63` conjunct** predates the receipts. It is harmless,
  and today's users (txn's `Reach`, the server's writer facts) use it. No change needed.

---

## What was checked and holds

- **The notify-step receipt** (`Txn.End` `Api.lean:540`, `Put` `:342-343`, `DeleteRange` `:363`, the
  lease-delete law's `End` `:902`): **provable.**
  - A write transaction's `idxWriter γ ilog pend` holds `⧖ (logCh ilog + pend.length)`
    (`InvIndex.lean:927-930`), which is `logCh (ilog ++ [pend])` since `logCh` sums lengths
    (`InvIndex.lean:906`).
  - The watchable `End` notifies while the transaction is still open (`s.notify` before
    `TxnWrite.End`), so the receipt is in hand at the notification.
  - A plain store fires both steps at the bump.
  - `pend = []` needs only `idxCert`'s whole-history receipt.
  - `⧖` is persistent (monoNat lower bound plus a pure fact).
- **`Restore` without receipt and length premises** (`Api.lean:416-436`):
  - the receipt comes from `mvccBackendFor` and is handed to the client at the commit (`:428`);
  - the length bound follows (F5 says where `receiptBound ≤ 2 ^ 48` must be recorded);
  - the server's `kvStoreInv` uses the commit's receipt (`σ'.notifiedLog = σ'.log`, since nothing is
    pending).
- **`mvccImage` soundness, given the code**:
  - the persistent receipt is global (one step counter per program), so the receiver may use the
    sender's;
  - a client can make an `mvccImage` only from fresh data or from a snapshot.
- **The Key-bucket part of the snapshot image under a concurrent compaction job**: provable.
  - The job deletes under the batch lock, and every commit (the run loop's, the job's
    `ForceCommit`, Snapshot's own) takes the lock.
  - The physical view is thin of the logical (`thinV`, `InvBackend.lean:678-680`): a missing key
    carries `dlIs`. mvcc's registration says that means "compaction at some `crevLb c` may delete
    it" (`storeDlReg`).
  - With F2's pin of `σ.crev`, that gives the partly compacted bucket `u` describes.
  - Only the compaction keys (F1) are out of reach.
- **The whole share excludes what changes the history.** `Write`'s begin does not change it, and
  `End`, `Put`, `DeleteRange`, `Compact` and `Restore` all take a share. Readers, the sync loops and
  the job do not change `σ`. An open write transaction holds the batch lock, so the snapshot's
  commit waits for an `End` that cannot happen (partial correctness, vacuous).
- **`reach_logWf.law`**: true by induction on `MvccReachable`. `notify` carries
  `LogWf (σ.log ++ [pend])`, `commitPending` gives `commitLog`, and `LogWf'.prefix`
  (`LogLemmas.lean:670-690`) covers the committed log while something is pending.
- **Positivity** (`kvSortOk`, `wsRecvOk`): true.
  - Revisions are at least 2 (revision 1 is empty in `mvccStart`, and `MvccReachable` keeps it).
  - A live key's version is at least 1.
  - None wraps: every value is at most `logCh` of the history, below `receiptBound ≤ 2 ^ 48`.
  - Deletes' `ModRevision` is patched in both sources (End and `kvsToEvents`).
- **The lease-delete law's `End` triple** matches `Txn.End.contract` at a write view: the same
  precondition minus the consumed `mvccTxn`, the same nested updates with the receipt, and the same
  post.

## Per target

### `Api.lean` / `ApiState.lean`

- **Good:**
  - one opaque persistent `mvccImage` replaces the pure `imageOf` and carries the receipt end to end,
    with no new client resource;
  - `Restore` is smaller;
  - every step that changes the history hands out the same receipt;
  - the snapshot law uses the API's existing update shape rather than a pin predicate.
- **Findings:** F1 (blocking), F2 (spec mitigation), F3, F4, F6, F7.

### Server draft (`ServerSpecs.lean`, `clients-server.md`)

- **Good:**
  - `kvStoreInv`'s receipt is maintained from the API's steps alone;
  - the builders are complete for every update shape;
  - the Restore builder covers the whole precondition;
  - the boot sequence's order is right (it needs F3's `|==>`, which it already runs under).
- **Assumes more than the API gives:**
  - G3 for compacting servers (F1). `senderImage.law` is unprovable there until F1 is fixed, and the
    note's "No obstacle found" should be withdrawn for that case.
  - `senderImage.law` hard-codes `on = false`. That is the deferred #7-on, not an API matter.
- **Shrinkable once F2's token exists:** `kvAus.law`'s third conjunct (`auSnap`) can go, as described
  under F2.

### Watch draft (`WatchSpecs.lean`, `clients-watch.md`)

- **Good:** nothing it uses goes beyond the API: `wsRecv_ok`, `wsChan_recv`, `wsSentLb`(`_zero`),
  `reach_logWf`, `shapes`.
- **Depends on the server:** `histLb_model.law` and the timeless peek.
- **Does not use:** `wsRecvOk`'s positivity (F6). No API change needed.

### Txn draft (`TxnSpecs.lean`, `clients-txn.md`)

- **Good:**
  - `commitAU` has `Txn.End`'s exact shape and passes the receipt through;
  - it keeps no invariant;
  - the sort premise comes from `Txn.Range`'s `stateOk`;
  - it uses only `kvSortOk_nonneg`.
- **Findings:** none.

### Invariants note (`notes/mvcc-api-invariants.md`)

- **Findings:** F2's device, F5's stale and missing items, and F1's backend ghost (`fkdAt` held in
  `compactRes`) once decided.

## Ranked by need of revision

1. `Api.lean`'s `mvccImage_snapshot.law`, with its premise `backend.Snapshot.spec`: F1 (user's
   decision: strengthen the axiom, or split a stronger trust-boundary spec), and F2's `isMvcc`.
2. `notes/mvcc-api-invariants.md`: F2's exclusion and freeze device, and F5.
3. `Api.lean`'s `mvccImage_fresh.law`: F3 (`|==>`).
4. The server draft: G3's claim (F1), and optionally `auSnap`.
5. `Api.lean`/`ApiState.lean` minimality: F4 (`keySized`), F6, F7.
6. The watch draft: none.
7. The txn draft: none.
