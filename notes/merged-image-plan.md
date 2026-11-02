# The merged snapshot's image: `merged_image` restated (2026-11-02)

Spec-first (`notes/spec-first-plan.md`): Scope, Draft, Review, then the user, then Freeze. The
finding is in `notes/decisions.md`, "`merged_image` is false with compaction on, and lacks the fresh
start's raft names". Branch `merged-image`.

## Scope

**Configuration.** The merged snapshot's image (`applyAll`'s `msgSnapC` branch, SNAPSHOT-SORRY #7)
is certified with the auth mode off **and the compaction mode off** (`E.cmp = false`), at a fresh
start (`γr.raft = ⟨γr.raft.raft, [], W64 0⟩`, which every server is: `NewServer`'s premise
`ρ.rd.raft = ⟨γ, [], W64 0⟩`). The compaction-mode image joins the auth-on one as an open branch
(`SNAPSHOT-SORRY #7-cmp` beside `#7-on`): certifying a compacted image (a `srvImage` allowing the
compaction keys and the keys compacted away) is a design question of its own, like `run_job_snap_cmp`
(J8b).

**The statements that change.**

1. `merged_image` (`SnapSendBranch.lean`, internal): two premises, `(hcmp : E.cmp = false)` and
   `(hraft : γr.raft = ⟨γr.raft.raft, [], W64 0⟩)`; the rest unchanged. Proved under them (draft
   `merged_image'`).
2. The fresh start's raft names reach `applyAll`'s batch case, one of two ways:
   - **(A)** `EtcdServer.applyAll.specBatch` gains the premise `γr.raft = ⟨γr.raft.raft, [], W64 0⟩`
     (as `specSnap` has); `run_job_body` gains it too, and `run` gives it (draft `fresh_raft_of_run`:
     `kvRun`'s `γr.raft.ai0 = ai₀`, `rnEnvOk`'s `pre`, `isServerRun`'s `HEr`).
   - **(B)** no premise changes: `isServerApplyAll`'s start values (`⌜γr.kv.c0 = W64 0 ∧ γr.kv.log0 =
     [[], []]⌝`, there since S1 for the merged image) and `srvApplyAllBuilt`'s gain
     `γr.raft = ⟨γr.raft.raft, [], W64 0⟩`; `NewServer` builds it from its premise (draft
     `fresh_raft_of_newServer`); `start` passes the conjunct through (its pattern `%Hkv0` is
     unchanged); both of `merged_image`'s callers take it from `Hkv0`. `isServerApplyAll` is in the
     precondition of `applyAll.spec`, `specSnap`, `specOn`, `snapshot`, `snapshotIfNeeded...`, so
     their preconditions are strengthened by a fact every caller holds; no binder or premise moves.
     Recommended: the fact sits with its siblings, for the same consumer, and no caller's glue grows.
3. `applyAll`'s proof (`EtcdServer__applyAll.lean`, `wp_proof`'s batch case): the merge branch splits
   on `E.cmp`: `false`, `merged_image`; `true`, `sorry -- SNAPSHOT-SORRY #7-cmp`. `specSnap`'s case
   (`ApplyAllSnap.lean`) has `hcmp` and `hraft` as premises already and passes them.

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
`interface/` files: neither statement is in a committed interface. `applyAll.spec` (=
`specBatch ∧ specSnap`) is linked (`Link.lean`'s `EtcdServer.wp_applyAll`) and used only by
`run.wp_proof`'s link; it is not an exported result. `merged_image`'s `sorry` is in the trust base of
eleven collections (`cachekv`, `compactkv`, `k8setcd3`, `leasekv`, `linkv3p`, `linkvtxn`, `m2`,
`putget`, `putget3`, `server`, `watchkv`), `compactkv`'s, a compaction-mode example, included: there the hole was
false. After the change `merged_image` is proved and `EtcdServer.applyAll.wp_proof` holds the new
named `sorry` (#7-cmp): the `sorry` count is unchanged, the names trade.

## Draft

`Proof/go_etcd_io/etcd/server/v3/etcdserver/MergedImageDraft.lean` (imported by nothing; no `axiom`,
no `sorry`; builds): `merged_image'` (proved), `EtcdServer.applyAll.specBatchR` (option A's text) and
`specBatchR_of_specBatch`, the glue `fresh_raft_of_run` (A) and `fresh_raft_of_newServer` (B).

## Review

(rounds below)
