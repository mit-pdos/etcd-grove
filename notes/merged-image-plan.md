# The merged snapshot's image: `merged_image` restated (2026-11-02)

Spec-first (`notes/spec-first-plan.md`): Scope, Draft, Review, then the user, then Freeze. The
finding is in `notes/decisions.md`, "`merged_image` is false with compaction on". Branch `merged-image`.

## Scope

**Configuration.** The merged snapshot's image (`applyAll`'s `msgSnapC` branch, SNAPSHOT-SORRY #7)
is certified with the auth mode off **and the compaction mode off** (`E.cmp = false`). Every server
is a fresh start (`isServer`'s `srvRaftLogInv`: `pre = []`, `ai0 = 0`), which `srvImage`'s
`⟨γ, [], 0⟩` needs. The compaction-mode image joins the auth-on one as an open branch
(`SNAPSHOT-SORRY #7-cmp` beside `#7-on`), and like `#7-on` it is false as stated: it asserts
`srvImage` of a snapshot that can hold `Meta`'s compaction keys. Its fix is the same shape as
`#7-on`'s accepted target (b) ("The merged snapshot's image with auth on"): `srvNet`'s image in the
cluster's mode; the compacted image's vocabulary is drafted (`mvcc.keyImageM`,
`M2StorageDraftRestore.lean`). The cluster's `cmp` is in `KVNames`, not `SrvRaft`, so `srvNet` would
need it: the user's decision (questions below).

**The statements that change.**

1. `merged_image` (`SnapSendBranch.lean`, internal): one premise more, `(hcmp : E.cmp = false)`;
   the rest unchanged. Proved under it (draft `merged_image'`), the fresh start's names from
   `isServer` by a new law `srvRaftLogInv_fresh` (`SrvRaftLog.lean`, beside `srvRaftLogInv_facts`).
2. The compaction-mode hole as a named lemma, `merged_image_cmp`: `merged_image`'s statement with
   `(hcmp : E.cmp = true)`, `sorry -- SNAPSHOT-SORRY #7-cmp`, its docstring saying it is false as
   stated (so that the trust-base report names it and the later fix is local).
3. `applyAll`'s proofs: the batch case (`EtcdServer__applyAll.lean`) splits on `E.cmp`
   (`merged_image` / `merged_image_cmp`); the snapshot case (`ApplyAllSnap.lean`) calls
   `merged_image` at `E'` with `E'.cmp = false` from `specSnap`'s `hcmp` and `beSucc` (`AEnv.onBe`
   keeps `cmp`).

No spec changes: `applyAll.specBatch`, `specSnap`, `isServerApplyAll` and `run` stay as they are.

**Why not a weaker `hcmp`** (the coordinator's question: "`Meta` has no compaction keys"). `keyImage`
needs both `noCmpData D` and the exact `Key` bucket; `mergedObs` gives the exact bucket only at
`cmp = false` (the job deletes keys). A premise "`noCmpData D` and the `Key` bucket exact" (or
`keyImage x.log D` itself) is the weakest true form, but no caller can give it with compaction on:
nothing tracks "no compaction applied yet" (in Go a compaction's `scheduledCompactRev` is written
before its deletions, so `noCmpData D` would imply the exact bucket, but `backend.Snapshot`'s
observation and the writer's laws do not say so; stating it is mvcc work). With compaction off, both
forms are given by `mergedObs`. So `hcmp` is what callers can use; the weaker form buys nothing now.

**Callers** (`etc/importers.py --uses`):
- `merged_image`: `EtcdServer__applyAll.lean` (batch case, `wp_proof`) and `ApplyAllSnap.lean`
  (`wp_proofSnap`, the snapshot case).
- `EtcdServer.applyAll.specBatch`: its proof (`EtcdServer__applyAll.lean`) and `EtcdServer__run.lean`
  (`run_job_body`, called by `run.wp_proof`'s job body); `SDRun.lean` names its `match_1` only.
  `run` is reached by the exported server results through `start`.

**Exported or linked.** The server package has no API list (`etc/api/` has `backend`, `raft`) and no
`interface/` files: no statement here is in a committed interface. `applyAll.spec` (=
`specBatch ∧ specSnap`) is linked (`Link.lean`'s `EtcdServer.wp_applyAll`) and used only by
`run.wp_proof`'s link; it is not an exported result, and it does not change. `merged_image`'s `sorry`
is in the trust base of eleven collections (`cachekv`, `compactkv`, `k8setcd3`, `leasekv`, `linkv3p`,
`linkvtxn`, `m2`, `putget`, `putget3`, `server`, `watchkv`). After the change those collections
trade `sorry merged_image` for `sorry merged_image_cmp` (`etc/tcb-baseline.txt`'s line and each
collection's, by `--check --update`): the count is unchanged. The reports list declarations, not
modes, so all eleven list the hole, which is false only in the compaction mode; two collections run
that mode and so rest on a false hole until #7-cmp is repaired: `compactkv` and `m2` (`putgetc_safe`:
`putgetc` runs the auto-compactor, `StartPeriodicServer` with `cmp := true`). Freeing the nine
mode-off collections of the hole would need a mode-gated spec, outside this stage.

## Draft

`Proof/go_etcd_io/etcd/server/v3/etcdserver/MergedImageDraft.lean` (imported by nothing; no `axiom`,
no `sorry`; builds): `srvRaftLogInv_fresh` and `merged_image'` (proved). No glue: no caller's
premises change.

## Review

**Round 1** (fresh `spec-reviewer`, commit 3972d557ab; the draft then also had `hraft` and two ways
of carrying it to `applyAll`'s batch case: (A) a `specBatch` premise, (B) a conjunct of
`isServerApplyAll`):
- R1/R2/R3 (first tier): `hraft` derivable from `isServer` (`srvRaftLogInv`'s `pre = []`,
  `ai0 = pre.length`); the finding's second item false; A and B unneeded. Taken: `hraft` dropped,
  derived by `srvRaftLogInv_fresh`; A, B and their glue deleted; the decision entry corrected.
- R4 (first tier): the proposed `#7-cmp` hole asserts something false, and the plan hid it. Taken:
  said in the plan and the decision; the hole as a named lemma, `merged_image_cmp`.
- R5: the truer alternative, a mode-indexed `srvNet` image (as `#7-on`'s target (b)). To the user.
- P1: the snapshot case's call is at `E'` (`E'.cmp` from `beSucc`). Taken in the plan.
- P2 (later): `specSnap`'s premises `γr.raft = ⟨…⟩`, `γr.kv.c0 = 0` are derivable from its
  `isServer`; `log0` is in its `isServerApplyAll`; `run_job_snap_cmp`/`run_job_body` thread the same
  facts. Candidates for removal in a later stage, not here.
- Also noted: `merged_image`'s `h0.1` (`c0 = 0`) is derivable (`kvInv`'s `c0 ≤ ai0`); `h0.2` is not.

**Round 2** (fresh `spec-reviewer`, commit 477dd3b96e, looking hardest at round 1's diff): no
first-tier finding on the statements (`merged_image'` true, every premise used, sufficient for both
callers; `srvRaftLogInv_fresh` correct).
- R2-1 (first tier, the record): not only `compactkv` runs the compaction mode; `putgetc` does too
  (`m2`'s `putgetc_safe`). Taken: the plan and the decision entry name both.
- R2-2: the plan cited the entry's old title. Fixed.
- P2-1: say which baselines move and that the static reports list the hole in all eleven. Taken.
- P1-1: `h0.1` (`c0 = 0`) derivable (`kvInv`'s `c0 ≤ ai0`). To the user (question 3).
- P1-3/P2-3: `merged_image` over `mvcc.keyImage x.log D` in place of `hcmp` (true in every mode),
  and the hole the pure `mergedObs γr true … → keyImage log D` (decidable, testable). To the user
  (question 2).
- P2-2: #7-cmp's fix in place (`imageAt`'s `keyImage` as `keyImageM γk.cmp`, `keyImageM_off`, per
  `compaction-in-place.md`) rather than a mode-indexed `srvNet`. To the user (question 4).
- P2-4 (wording, taken), P2-5 (`AEnv.onBe`'s docstring should list `cmp`, `cret`: at Freeze).

## Questions for the user (before Freeze)

1. Freeze `merged_image` with the one premise `hcmp : E.cmp = false`, the law `srvRaftLogInv_fresh`,
   and the batch case's split onto a named `merged_image_cmp` (false as stated, SNAPSHOT-SORRY
   #7-cmp)? Recommended: yes.
2. The hole's form: `merged_image_cmp` (the image certificate at `E.cmp = true`), or `merged_image`
   over `mvcc.keyImage x.log D` with the hole the pure `mergedObs γr true … → keyImage log D`?
   Recommended: the pure form (the lemma true in every mode, the false claim a decidable fact about
   the snapshot), unless the in-place fix (4) comes soon, which replaces either.
3. Drop `h0.1` (`γr.kv.c0 = 0`, derivable from `isServer`)? Recommended: no, not in this stage
   (callers hold it; the change would touch both call sites for no gain); with `specSnap`'s
   derivable premises (round 1's P2) in a later cleanup.
4. #7-cmp's repair: the image in the cluster's compaction mode, in place (`imageAt`'s `keyImage` as
   `mvcc.keyImageM γk.cmp`, `keyImageM_off` the "off is today's" law) or a mode-indexed `srvNet`
   (#7-on's target (b))? Recommended: in place, together with #7-on's, as its own stage.
