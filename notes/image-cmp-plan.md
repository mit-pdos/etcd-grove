# The image certificate by the mode: #7-cmp (2026-11-02)

Spec-first (`notes/spec-first-plan.md`): Scope, Draft, Review, then the user, then Freeze. Branch
`image-cmp` (on `m2-item15`). The user's direction (`notes/decisions.md`, "`merged_image` is false
with compaction on", accepted 4): repair SNAPSHOT-SORRY #7-cmp in place, `imageAt`'s `keyImage` as
`mvcc.keyImageM γk.cmp`, `keyImageM_off` stating that the mode off is today's image. The draft is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/ImageCmpDraft.lean` (imported by nothing; no axiom, no
`sorry`; it builds).

## Scope

**The chain.** `srvNet γ`'s `img` is `srvImage γ i D` (`InvApplyAll.lean`): some KV names `γk` at the
fresh start values (`c0 = 0`, `ch0`, `log0 = [[], []]`) with `dbImage ⟨γ, [], 0⟩ γk i D`, which is a
committed log `A` (`srvRLogLb`), `i = ai0 + |A|`, and `imageAt γk boot i (pre ++ A) A D`
(`InvImage.lean`): `mvcc.keyImage (kvModel γk A) D` (the `Key` bucket exactly the log's, `Meta`
without compaction records), the consistent index and a term in `Meta`, the rest buckets
(`bkRestAt`), `IdxWf`. `γk.cmp` is not read.

**Producers.** `merged_image` (`SnapSendBranch.lean`, mode off, proved) and `merged_image_cmp`
(mode on, `sorry -- SNAPSHOT-SORRY #7-cmp`, false as stated), both called from `applyAll`'s batch
case (`EtcdServer__applyAll.lean`, split on `E.cmp`) and the mode-off one from the snapshot case
(`ApplyAllSnap.lean`). The window `mergedCreate_window` gives `mergedObs`, whose `Key` and
`noCmpData` clauses hold only at `cmp = false`.

**Consumers.** `snapRecv_image` (`SnapRecvFacts.lean`) turns the network's certificate into the
image facts `applySnapshot.specSnap` takes (since M2 item 15: `r`, `hcc`, `hkI : keyImageM d.cm …`,
and in its pre `restoreRcptM d L`, `crevPermAt E.γ r.finRev`, `crevPermAt E.γ r.crev`). The snapshot
directory's `snapDirInv` (`InvRun`/`SnapRO`) and rafthttp's `Net` axioms are generic in `N.img`.
`NewServer`'s trusted premise `γn.N = srvNet γ`: its text stays, its meaning changes with
`srvImage`.

**The Go code** (fork pin, etcd `ab3c28d9a`). `createMergedSnapshotMessage` commits the store and
takes `be.Snapshot()`; `updateCompactRev` sets `compactMainRev` and writes `scheduledCompactRev`
with a `ForceCommit` under `revMu` before the job runs; `scheduleCompaction` deletes, in batches each
`ForceCommit`ted, the `Key` entries at or below `compactMainRev` that the compaction does not keep,
in revision order, and writes `finishedCompactRev` with the last batch; `restore()` reads both
records and resumes `scheduledCompactRev` when it is above `finishedCompactRev`. So a snapshot
holds, at `r.crev = compactMainRev` (the latest compaction applied, `crevOf γk A` of the model), the
log's entries less, per key, a prefix of those the compaction at `r.crev` deletes: `keyImageM`-on's
`entsCutAt`. Checked by a Go test (scratchpad, `axiomcx/imgcmp_test.go`, `TestImageCmpMidJob`:
snapshots mid-job and with a second compaction scheduled behind the first, both `crev` the latest
compaction and the cut per key a prefix).

**`srvNet`'s image and `srvImageR`.** B2's `dbImageR`/`srvImageR` (`M2StorageDraftB2.lean`) add the
receipt `⧖ (logCh (kvModel γk A))` that `restoreRcptM` needs on. The draft adopts it in place
(`dbImageD`): one certificate, not two; `srvNet`'s text stays `img := srvImage γ`.

## Draft (`ImageCmpDraft.lean`)

1. **`imageAtD`** (draft of `imageAt`): `∃ r, keyImageM γk.cmp (kvModel γk A) r D ∧ r.crev = crevOf γk A`
   in place of `keyImage (kvModel γk A) D`; the rest unchanged. `imageAtD_off`: with `γk.cmp =
   false`, `imageAtD ↔ imageAt ∧ crevOf γk A = -1` (`keyImageM_off`). The `crevOf` conjunct is what
   pins the records to the model: without it, a mode-on image at `r.crev = -1` of a log with a
   compaction would be a different (and Go-false) image, and the receiver's `hcc` would have nothing
   to stand on.
2. **`dbImageD`, `srvImageD`**: today's texts over `imageAtD`, `dbImageD` with the receipt
   `⧖ (logCh (kvModel γk A))`.
3. **No mode in the network's certificate.** `srvImage`'s existential `γk` fixes the start values,
   not `cmp`: `dbImageD_of_srvImageD` gives `dbImageD` at `{γk with cmp := b}` for some `b`. A
   receiver moves the image to its own mode by `keyImageM_mode` (on → off needs `r.crev = -1`;
   off → on always), through `imageAtD_kv_congr`. The receiver's own mode off gives `crevOf γk A' =
   -1` of its committed log (`crevOf_off`, from `kv_log_plain` and `crevOf_plain`). So `SrvRaft`
   and `srvNet` need no mode (the alternative, a mode in `srvNet`, is the auth-on #7-on's target
   (b); not needed here).
4. **The sender, `merged_imageD`** (in place of both `merged_image` and `merged_image_cmp`): from
   `mergedObsD γr E.cmp ai A x.log x.crev D` (the window's observation restated: the image by the
   store's mode at records of revision `x.crev`; today's `Key` and `noCmpData` clauses gone), the
   sole writer's receipt `⧖ (logCh x.log)`, and `hcrev : x.crev = crevOf γr.kv A`. Proved (mirrors
   `merged_image`; the mode tie `γr.kv.cmp = E.cmp` from `srvKVInvs`). Off, today's window gives the
   draft's observation (`mergedObsD_of_off`, at `x.crev = -1`).
5. **The receiver, `snapRecv_imageMD`** (the glue at `specSnap`'s call): from `srvKVInvs E γr`,
   `srvImageD γ i D` and the receiver's `srvRLogLb γr.raft A'` (`|A'| = i`), with `E.γ.kb = some d`
   and `CrevPermitLaw`: some `r` with `keyImageM d.cm (kvModel γr.kv A') r D ∧ r.crev = crevOf γr.kv
   A'`, `restoreRcptM d (kvModel γr.kv A')`, `crevPermAt E.γ r.finRev`, `crevPermAt E.γ r.crev`.
   Proved. `specSnap`'s `hcc` follows by `crev_hcc` (from `kvApplied`'s `x.crev = crevOf γr.kv A`
   and `A <+: A'`); the equation is also what re-forms `kvApplied`'s clause at `A'` after the restore
   (`x'.crev = r.crev`) and what a later `merged_imageD` from the restored member needs.
6. **The permits are derived, not carried** (56's question). The certificate does not hold
   `crevPermAt`: a permit is `kvCmpPermit γk c = 0 < c ∗ kvRevLbZ γk (c + γk.cret)`, at the
   receiver's KV names (its `cret`, its revision ghost), which the network's certificate (existential
   names) cannot name. The receiver derives them: its store's `crevPermIs E.γ (kvCmpPermit γr.kv)`
   (`srvKVInvs`) and `CrevPermitLaw` (a law to prove: the committed log's `crevOf` is `-1` or a
   committed compaction's revision, permitted by `cmpLogOk`, `cmpPermRq_of_entry`'s argument at
   `crevOf`); `r.finRev ≤ r.crev` (`CmpRecs.finRev_le_crev`) and `recsPos` give the finished
   record's permit by `kvCmpPermit_le`.

## What the Prove phase needs (not drafted)

- **The sender's observation in the mode on** (`mergedCreate_window` restated to give
  `mergedObsD` and `⧖ (logCh x.log)`). Today nothing gives it: `backend.Snapshot.spec` (an axiom,
  `backend__Snapshot.lean`) observes `vData` (no hook bucket: `Meta` is one), `hkData`, `rbData`,
  and its post's `fkRd` gives only the flag lower bound and the values at open; the store does not
  track the job's progress (per key, a prefix of the deletable entries, deleted in revision order)
  nor the records' values. Needed: mvcc's tracking of the records (`scheduledCompactRev` =
  `compactMainRev` = `x.crev`, `finishedCompactRev` of the last finished job) and of the job's cut
  (`entsCutAt` at `x.crev`), and the backend's hook-key values in the snapshot's observation (a
  restated `Snapshot` axiom: an axiom check, `axiomcx`). The receipt: the sole writer's `idxCert`
  gives `⧖ (logCh log)` (`InvIndex.lean`), the window's post to hand it out.
- **`kvApplied`'s clause `x.crev = crevOf γk A`** (deferred in M2's apply Draft, "stage 4c"; M2
  apply item 17 already says the certificate must carry `r.crev = crevOf γk A'`): `crevOf` moves
  from `M2ApplyDraft.lean` to a real module.
- **`CrevPermitLaw`**, proved from `kvInv`'s `cmpLogOk`.

## Impact (at the switch)

Restated in place: `imageAt`, `dbImage`, `srvImage` (`InvImage.lean`) and their congruence lemmas;
`mergedObs`, `mergedCreate_window`, `merged_image` (`merged_image_cmp` deleted) in
`SnapSendBranch.lean`; `applyAll`'s batch case (no split on `E.cmp`) and snapshot case
(`ApplyAllSnap.lean`: the call at `E'`, either mode); `snapRecv_image`/`SnapImageFacts` and
`specSnap`'s caller (`SnapRecvFacts.lean`) over `snapRecv_imageMD`; `kvApplied` (InvRequest). Text
unchanged, meaning changed: `srvNet` (`InvApplyAll.lean`), `NewServer`'s trusted premise `γn.N =
srvNet γ` and the examples' specs that name `srvNet` (`Alloc`, `newServerMode`, ...),
`snapDirInv`. **The restart path reads `imageAt` too** (review round 2): `srvDiskImage`
(`InvRestart.lean:110`, the post of the drafted `EtcdServer.HardStop.spec` and of restart3's
`stop`, `startMember`, `BuildServer` specs) and `bootstrapRestartContract` (`InvRestart.lean:354`,
`examples/common/Restart.lean`): restated in place they need, of a stopped member's disk image, the
records at `crevOf` of its applied log (believed true: the consistent index is committed with
`updateCompactRev`'s `ForceCommit`; not checked), and a restart in compaction mode will need the
receipt there too (`srvDiskImage` has none): an open item of the restart path, not of this stage.
Trusted text: none changes unless the Prove phase restates `backend.Snapshot.spec`.
Collections whose baseline loses `merged_image_cmp`'s `sorry` once proved: `compactkv`, `m2`
(`putgetc_safe`), `cachekv`, and the eleven listing `merged_image`.

## Findings

- **F1. `keyImageM`-on's `NoDelPutAt` conjunct is false of a legitimate image.** A revision that
  deletes a key and puts it again (one `store.Write`; the server admits it, only v3rpc's check
  refuses it), compacted at that revision: the image keeps the put, `crev` is that revision, and
  `NoDelPutAt L crev` fails (`TestImageCmpDelPut`). The server's KV invariant does not track it, and
  `store.Restore`'s proof does not use it (`obtain ⟨hrec, -, hcut, -⟩`). A sender cannot give it.
- **F2.** The sender's observation in the mode on needs backend and mvcc work (above).
- **F3.** `kvApplied`'s deferred `crevOf` clause becomes needed on both sides.

## Review

Round 1 (a fresh `spec-reviewer`, given the targets, the Go code and the callers):
- Tier 1: `NoDelPutAt` in `keyImageM`-on (= F1 above, confirmed; the fix is 56's, a question); the
  receiver's glue proved `r.crev = crevOf γr.kv A'` but returned only `hcc`, while the restore's
  `x'.crev = r.crev` needs the equation to re-form `kvApplied`'s clause (and a restored member's
  next `merged_imageD` its `hcrev`): fixed, the post returns the equation, `hcc` by `crev_hcc`.
- Tier 2: `CrevPermitLaw` a premise (to prove at the switch; the reviewer finds it provable from
  `cmpEntryOk` and `kvInv`'s `γk.rlog = γ.raft.log`); `d.cm = E.cmp` derivable from `srvKVInvs`'s
  `kbCmpM` tie and `E.γ.kb = some d` (fixed: the glue takes `hkb`); `merged_imageD` over `isServer`
  using only `srvKVInvs` (fixed).
- Tier 3: `imageAtD` could read `keyImageM true` always (the network's certificate leaves the mode
  free anyway; a question); fold the glue into `snapRecv_image`/`SnapImageFacts` at the switch (one
  destructuring of the certificate; planned); `mergedObsD_of_off` at any `crev = -1` (fixed).
- Confirmed: the Go facts (records, cut, `crev` the latest compaction, also with a second compaction
  queued), all four sender/receiver mode combinations, the unconditional receipt, the mode out of
  `srvNet`, the permits derived rather than carried.

Round 2 (a fresh `spec-reviewer`): no new first-tier finding; F1 repeated (open, a question). New:
the restart path's readers of `imageAt` (above, Impact); `CrevPermitLaw` is true (by induction on
`A`: where `crevOf` rises the entry is a compaction, `kv_entry_claim` gives `0 < r` and `r + cret <
|kvModel (A.take j)|`, `kv_revLbZ_of_rlogLb` the lower bound), to prove at the switch and drop
`hperm`; `merged_imageD`'s and `crev_hcc`'s `hcrev` from `kvApplied` once it carries the clause;
the glue folded into `snapRecv_image` (`A'`, `hlA`, `srvRLogLb A'` then come from one opening of
the certificate); a law at the member's names (`srvImageD ⊢ … dbImageD` at the member's own `γk`,
the mode moved with `crevOf_offM`) for both readers of the snapshot directory's image; the pure
laws to mvcc (`CmpRecs`, `keyImageM_mode`, a `keyImageM_recsPos`), `restoreRcptM_on`/`_off` in
place of unfolding, `kvCmpPermit_le` beside `kvCmpPermit`; retire `M2StorageDraftB2`'s
`dbImageR`/`srvImageR` at the switch; a docstring fixed. Confirmed: the Go facts again (whole
batches only, `crev` also after a restore that resumed a compaction), mixed-mode clusters handled
(a mode-off member's `kvInv` rules out committed compactions), the receipt in the certificate (a
receiver's own `idxCert` covers only its shorter log), the permits derived.

## Questions (for the user; recommendations)

1. **Freeze the certificate as drafted** (`imageAt`'s key view `∃ r, keyImageM γk.cmp (kvModel γk A)
   r D ∧ r.crev = crevOf γk A`; `dbImage` with the receipt; `srvNet`'s text unchanged). Recommended.
2. **`keyImageM γk.cmp` or `keyImageM true`** in `imageAt` (both reviewers' third-tier point: with
   the `crevOf` conjunct the two are interchangeable, and `true` drops the mode from the
   congruence laws and the `∃ b` of `dbImageD_of_srvImageD`). Recommendation: keep `γk.cmp` (the
   user's direction; off reads as today's image by `imageAtD_off`), with a law at the member's
   names hiding the `∃ b`.
3. **Drop `NoDelPutAt` from `keyImageM`-on and `restoreImageM`** (F1, first tier in both rounds;
   56's definitions). Recommended: false of a legitimate image, unused by `store.Restore`'s proof,
   dropped from mvcc's compaction specs since item 18. Without it, `mergedObsD` on is unprovable.
4. **The permits derived at the receiver** (`CrevPermitLaw`, proved at the switch), not carried in
   the certificate. Recommended.
5. **The receipt in `dbImage` in place**, retiring B2's `dbImageR`/`srvImageR`. Recommended.
6. **`kvApplied` gains `x.crev = crevOf γk A`, `crevOf` moves to a real module** (M2 apply's
   deferred clause), in this stage's Prove phase. Recommended.
7. **The sender's mode-on observation**: mvcc tracking of the records and the job's cut, and a
   restated `backend.Snapshot.spec` observing `Meta`'s hook keys (an axiom check). Recommended as
   the Prove phase's main item, possibly its own stage.
8. **The restart path's `imageAt` readers** (`srvDiskImage`, `bootstrapRestartContract`) restated in
   place with it; their compaction-mode receipt left to the restart path. Recommended.
