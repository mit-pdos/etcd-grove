# Per-type stage B: handoff (2026-11-11)

Stage B fixes the grpc handler-pool soundness bug (`notes/STATUS.md`, "Soundness bugs: grpc.serve's
handler pool"). Coordinator: etcd-grove-81. Worktree `/shared/etcd-grove-stageB`, branch `stage-b`, cut
from `lean` `5fde200c15`. Scratch: `/shared/tmp/stageB/`.

## Done

- **Scope revision 5**: `/shared/tmp/stageB/scope-r5.md` (folds in review `wf_b189d821-c60` and
  etcd-grove-81's decisions; §1 is the changes table). r4: `scope-r4.md`.
- **B0** (in progress; no Lean statement on `lean`):
  - Go tests T1-T12, T5b, T8b, T9b: `examples/stageb/grpcruns/grpcruns_test.go`, all pass
    (`cd examples && systemd-run --scope -q -p MemoryMax=32G env GOWORK=off TMPDIR=/shared/tmp
    PATH=/usr/local/go/bin:$HOME/go/bin:$PATH go test -count=1 -v ./stageb/grpcruns/`).
  - Census script: `etc/stageb-census.py` (sections bounds, pools, lessor, handlers, start, consts;
    output in `/shared/tmp/stageB/census.txt`).
  - Spike: `Scratch/StageB/Spike.lean` (scratch, NOT in any lean_lib glob; must not land): the adapter
    with one `£ 1` (A4-MAJ-3), the carrier's identification (agree + joint Nodup), the fork over a
    model-only `#` name. Check: `env LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
    etc/lean-check.py -a Scratch/StageB/Spike.lean`.

  - Spike (4) done: `spike_grpcFullName_inj`, `spike_names_nodup`, `spike_v3rpc_nodup` (etcd's lists in
    `v3rpc.Server`'s registration order, from `svcDescsOk`'s facts and the restated health post).
  - goose `trusted = ["Server.Serve"]` dry run: works (scratch `/shared/tmp/stageB/goose-dry/`; needs
    `GOWORK` unset; adds `ptr_Serve_unfold`; `Server` is axiomatized, the model cannot name its
    fields). `etc/verified-code.py` counts a trusted function proved over its model as "verified":
    B1a must make the `Serve` model's leaves count as assumed.
  - Statements touching B's names: `/shared/tmp/stageB/stmt/stmtlist.md` (script `stmtlist.py`).

  - Full build clean (retry after one exit 143 while queued; 2nd run exit 0); `etc/tcb-report.py
    --check` matches the baseline (865 axioms, 5 sorries). Reach: 74 of 5179 roots rest on
    `grpc.serve`/`grpc.serveStream`, 18 of them `*_safe`.

## Next, in order

1. (done)
2. Gate report-only (`etc/AxiomTokCheck.lean`, `etc/axiom-tok-check.py`), import-all memory probe,
   fresh `tcb.json` (a subagent was on it).
3. goose `trusted = ["Server.Serve"]` dry run (a subagent was on it).
4. stmtdiff list of exported statements (`/shared/tmp/ptm-cp3/stmtdiff.py`).
5. CP0 report; STOP. B1a waits for the coordinator's go.

## Pitfalls

- Every lake command: `--packages=/shared/tmp/manifest-ddc.json`; full builds under
  `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G`
  (`/shared/tmp/stageB/fullbuild.sh`).
- `Scratch/` is a lean-check-only directory; delete it before any landing.
- The examples pin etcd at `a4d2bb1720b9` (not `673da07c8f` as the brief said).
