# out_size: handoff

Worktree `/shared/etcd-grove-outsize`, branch `out-size` (off lean `2004e1b2d1`). Scope:
`/shared/tmp/out-size/scope.md` (decisions D1-D7 approved, recorded in the worktree's `questions.md`,
untracked, with the forms decided). Coordinator: etcd-grove-81 (rules:
`/shared/tmp/coord-81/common-rules.md`). Goal: delete the `sorry` in `out_size`
(`Proof/go_etcd_io/raft/v3/MsgOut.lean`), its text unchanged; tcb 5 → 4.

## Build

```
export TMPDIR=/shared/tmp
# targeted (no flock):
systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <modules>
# full:
timeout 14000 flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G \
  lake build --packages=/shared/tmp/manifest-ddc.json
LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py -q -a FILE...
```

Targets for raft's log: `etc/importers.py --uses Huents --uses Hents --uses ownUnstable --uses
unstableOf Proof/go_etcd_io/raft/v3/InvRaftlog.lean` (list in `/shared/tmp/out-size/p1-raft.txt`).

## Done

- **C1 (P0 vocabulary, P1 log)**, 2026-11-12:
  - `PbSized.lean` (new, importable): `entBytes`/`entSizeOk` (moved from `MsgOut`), `entRZ sz l e`
    (a frozen entry at a content, `entSizeOk` when `sz`), `entsPtsZ`/`entsROz` and the slicing laws
    (`entsBigZ_*`, `entsPtsZ_*`), the `sz = false` bridges (`entsPts_entsPtsZ`, `entsPtsZ_false`,
    `ite_entsPtsZ_false`).
  - `PbContent`: `entRoC` and the entry lemmas generic in `hlc`.
  - `UnstableSt.sz` (default `false`); `ownUnstable` holds `entsROz us.sz`; `unstableOf` passes
    `false`; `ownRaftLog`/`ownRaftLogW` hold `entsROz false` (the node's flag `LogState.sz` comes at
    P4).
  - unstable specs: `nextEntries`/`slice` posts `entsROz us.sz`, `truncateAndAppend` over
    `entsPtsZ us.sz`, `restore` keeps `sz`. raftLog's specs unchanged (`append` converts with
    `entsPts_entsPtsZ`; `slice`, `nextUnstableEnts` weaken with `entsROz_entsRO`).

## Next, in order (Scope §4)

1. C1 committed (`12bc0aafa5`): full build green (17484 jobs), interfaces regenerated (all
   `etc/api/*.txt --check` clean), gates all ok but `k8s client error types` (StartCluster failed in
   0.04s under the parallel gate run; the same test alone passes, 212s). Waiting for the
   coordinator's go for `etc/land.sh` (merge lean first; STATUS entry and session registry then).
2. P0's law part, moved to P3: `outSetR` with the pure fact, `raftOutInv_insert`'s premise.
3. C2 (statements Freeze, hard stop): storage contract with `sized` and the cut (the cut needs the
   contents as a list: use `∃ cs` with `entRoC`, and a bridge `entsROz sz s es ⊢ ∃ cs, …` by
   induction, as `entsRO_entsRoC`), `MemoryStorage.Append`, starters, `isRNMemStor`, `outSetR`,
   the restart clause (+ `axiom`-skill review).
4. P2-P5 (raft), C3; P6, P7 (tell etcd-grove-81 before P7: D7), C4; C5.

## Pitfalls

- `notes/status-history.md` is append-only.
- Never `GOWORK=off` in the shell running `etc/land.sh`/`gates.sh`/`goose.py`.
- Python replace of a 4-space line also matches inside a 6-space one: anchor replacements.
