# Restart S7 (restart1): handoff (2026-11-14)

Worktree `/shared/etcd-grove-rs56`, branch `restart-s7` (off `lean`). Plan: `notes/restart-s7-scope.md`
(approved 2026-11-14, its "Approved" section). Probe report: `notes/restart-s7-probe.md`.

## Done
- The approvals recorded (`notes/restart-s7-scope.md`, `questions.md`); `notes/restart-scope.md`'s table: S7 is
  restart1, R2s-A keeps its name.
- **S7.0 (CP-a):** `examples/etcd/restart1/restart1.go` (one member, `NPuts = 11` in-process `Put`s of keys
  `"k"+byte(i)`, the `AppliedIndex()` wait, `HardStop`, `BuildServer` + `Start` again, a `Leader() != 0` wait,
  one in-process linearizable `Range` of `["k", "l")` checked exactly), `restart1_test.go` (`TestMemberID`,
  `TestRun`: counts the restart's log messages and fields), project `restart1` in `etc/goose.py`, the
  translation `Code/.../examples/etcd/restart1.lean`, `GeneratedProof/.../restart1.lean` (built).
  Test: 20/20 runs pass in separate processes; WAL snapshot record at index 14, backend kept at consistent
  index 15 (19/20; 1/20 at 14 = the last entry), commit 15, no snapshot sent.
- **S7.1 (CP-b):** `Scratch/S7Probe.lean` (untracked; probes P1-P4, checked) and the report.

- **Landed** S7.0 + notes: `lean` `19cd2cb540` (2026-11-14).
- **S7.2' (P3), done** (`7560eecea4`): `memberBuiltR` in `NewServer.specR`'s post shape; `wp_Start_builtR`
  proved from `Start.spec`; `Start_builtR_spec` deleted (restart3's `startMember.wp_proofRestart` uses
  `wp_Start_builtR`). Restarted-lessor check: `srvLeaseRd` in the mode `none` also accepts `lease.srvInvAt`
  at the recovered snapshot (laws `srvLeaseRd_of_srvInv`, `_of_srvInvAt`, `_srvInv`).
- **P4-a statement, done** (same commit): `memberRestartFacts` in `BuildServer.specRestart`'s precondition,
  `memberBoot_restartFacts`; restart3's draft `startMember.specRestart`/`restartCheck.spec` carry it.
  `BuildServer.specRestart`'s proof is S7.4, not started.
- **Landed** S7.2' + P4-a statement: `lean` `5355352d5d` (2026-11-14; the first try failed the mode gate:
  `srvErM false` literals, now `srvEr`, definitionally equal).
- **P2-a, WIP** (`de74cd8d84`, not landed): the protocol's `MsgSnap` carries `snapDstOk` (raft builds through its
  `Link`; server not rebuilt yet, a full build). Stopped on the row-4 finding (`notes/restart-s7-p2a.md`,
  "Progress and a finding"): option (A) approved and done in raft (`5d6d93926b`, `fb42ba546e`, then the
  server's `InvRaftNode` patterns); raft builds through `Link`/`Results`, the server's `InvRaftNode` and
  `EtcdServer__run` build; no full build yet. Second stop (same note, "Option (A), done in raft, and a second
  stop"): the rows are plain wands under a basic update, but the destination fact reaches `To = id` only
  through fancy updates; waiting for etcd-grove-81 on restating the rows with a fancy update.

- **srvLeaseRd consumer check** (etcd-grove-81's condition on the change, 2026-11-14):
  `etc/importers.py --uses srvLeaseRd` lists `etcdstart.{Defs,Restart,Served,ServedLease,newServerMode}`;
  with the laws' users (`srvLeaseRd_lessorRd`, `srvLeaseRd_srvInv`, `lease.srvInv_first`): `Served` passes it
  through (`memberUp_served`); `newServerMode` and `Restart` build it; `ServedLease`'s mode-`none` branch takes
  only the reader side (`srvLeaseRd_lessorRd`), its `mono`/`revocable` branches go through
  `srvLeaseRd_srvInv` (`m ≠ none`, the empty start); the lease-expiry example (`revocable`) reads the empty
  first snapshot through `srvLeaseRd_srvInv` then `lease.srvInv_first`. **No mode-`none` consumer relies on the
  empty start.**

- **P2-a done** (2026-11-14, `acfa82c7ff`, interfaces `3fe663255f`): rows as fancy updates, `srvRestartRows_single`
  (`RestartRowsSingle.lean`); full build OK (flock, 64G); tcb unchanged (870, 4); bounds/mode/api/layout ok.
  Waiting for etcd-grove-81's review of the interface diff (`/shared/tmp/restart-s7/p2a-interface.diff`), then land.

- **Weaker exported lemmas (P2-a; the review's item 5)**: lemmas of raft's importable protocol modules took
  extra premises: `replOk_message` (the step's configuration `c`, its destination fact, `cfgCommitted`),
  `ownRaftGhost_step_win`/`_send_apps` (the destination fact), `outMsgOk_self`/`outMsgOk_pend` (the message
  is no snapshot), `outboxRelP_isRaftMsg(_gen)`/`outboxRelP_isRaftMsgs` (`SnapNotSelf`); and `isMessage`'s
  `.snap` clause, `outMsgOk`'s waiting disjunct and `isRaftMsg` each gained a conjunct. Nothing outside raft
  uses them (the independent review checked: no client-visible fact weaker outside raft).

- **Landed** P2-a: `lean` `7c9a02aec4` (2026-11-14).
- **S7.4 question (stop)**: `BuildServer.specRestart` calls `NewServer.specR`, whose premise
  `srvRestartRows γ id A σ` is at the image's witnesses `A σ`, which only the proof learns (it opens
  `srvDiskImage`). Its precondition has no such resource. Options: (i) add `□ ∀ A σ, srvRestartRows γ id A σ`
  to the precondition (restart1 discharges it with `srvRestartRows_single`; restart3's draft carries it);
  (ii) specialize to one member (`ps = [id]`) and discharge it inside with `srvRestartRows_single` from
  `memberRestartFacts`' `srvRaftLogInv`. Both add a premise that reaches `etcd_restart1_safe` (true by
  construction there). Recommended: (i), general and honest; restart3 keeps its open row.

- **S7.4 started** (2026-11-14): option (i) in (`BuildServer.specRestart` takes `□ ∀ A σ, srvRestartRows γ id A σ`;
  restart3's `startMember.specRestart`/`restartCheck.spec` carry it, `Run.wp_proof` takes it as a hypothesis
  `hRows`, its open row, R2s-A removes it). Not landed.
- **S7.4 plan for the proof** (next agent):
  1. `newServerMode.specRestart` (retention 0, revision mode, `cmp = false`, auth off) over
     `NewServer.specR`, mirroring `newServerMode.wp_proof`; `newServer.specRestart`; `BuildServer.wp_proofRestart`.
  2. Inside, from the precondition: open `memberRestartRes_boot` → `srvDiskImage` → its witnesses
     (`S σ i A D m M`) for `srvDiskImageAt`; `Hrows` at those `A σ`; `memberRestartFacts` → `srvRaftLogInv`,
     `idClusterInv`, `idNoZero`, `srvPropMint`/`srvRdCtxInv` (carry over: `Scratch/S7Probe.lean`'s
     `probe_P4_mint`/`probe_P4_rdctx`, to be made laws), `kvInv` (→ `kvInvM false` by `kvInv_restartNames`).
  3. Allocate the incarnation's names (ghost updates in the proof): `idIncarnation_alloc` (the key's entry,
     wait token, fact at the new `E₀'.γs.slog`), the slot/pending maps (`idShare`'s other two auths), a fresh
     `KVSNames` for `newServerStoreFreshA`, `cok`, `γrev`, the read names' fresh rows (`srvReadNamesFreshNK`:
     applied, committed, notifier, logs, pend, `kv.hi`), with `ρ'.rd.raft = ρ.rd.raft`, `ρ'.rd.kv` the old
     names but `hi`/`cok`, so that `restartNames ρ ρ'` (check `kvCongr`'s fields).
  4. **Gap found**: `envVerifyOff` (`NewServer.specR`'s `#Hvoff`) comes at a first start from
     `memberFreshRes_verify`; `memberRestartRes` lacks it. Proposal (form): add `envVerifyOff` to
     `BuildServer.specRestart`'s precondition (persistent; the driver keeps it from the first start's fresh
     bundle; the same world assumption `verifyEnvOff` the closed theorems already take).

- **S7.4 done** (2026-11-14, `9d8786af86`, `99591c7ae4`, not landed): `BuildServer.specRestart` takes
  `envVerifyOff` (approved by etcd-grove-81; restart3's drafts carry it, `Run` keeps it from member 2's fresh
  bundle, `memberFreshRes_verify`); `newServerMode.specRestart`/`newServer.specRestart` (retention `0`) and
  `newServerMode.wp_proofRestart` over `NewServer.specR`, `newServer.wp_proofRestart`,
  `BuildServer.wp_proofRestart`, linked in etcdstart's `Link.lean` (`wp_BuildServerRestart`, `+Restart` in
  `etc/link-lean-first-common.txt`). The restarted names: `memberRestartFacts_alloc` (`Restart.lean`;
  `restartReqNames`, `memberRestartBoot`): `idIncarnation_alloc` at a new key, new slot/pending maps, read
  names' rows, `cok`, `hi`, a fresh store (`newServerNames_alloc`), `env₀`; `restartNames` by `rfl`. The
  carry-over probes P4 are `srvPropMint_congr`/`rfl` rewrites inside it. **Form:** `memberRestartFacts`
  gained `∃ x, idKeyFactAt ρ.ids.fs ρ.ids.key x` (from `memberBoot`'s), because `idIncarnation_alloc` needs
  `idPfxOk` of the prefix, which `idKeyFact_pfxOk` reads off the claims' invariant.

## Next, in order
1. Land S7.4 (after etcd-grove-81's go): full build, interfaces (`etc/gen-interface.py etc/api/etcdstart.txt`,
   `--layout --update` for the two new `specRestart`s), tcb `--check`, then `etc/land.sh`.
2. S7.5: the example's proofs (P1's three lemmas), link, adequacy, `Results.lean`, collection; Freeze of the
   theorem before its proof is linked. `etc/gen-init.py`'s `ROOTS` gets the package then.

## Pitfalls
- Run the Go test once per process (`go test -c`, then the binary per run): Run leaves the restarted member
  running, and a second `TestRun` in the same process deletes its directory under it (`failed to release wal`).
- Without the `Leader()` wait, the restarted member's first linearizable read fails with `leader changed`.
- GOWORK=off for the Go tests only; never for `etc/goose.py`/`etc/land.sh`.

## Commands
- Go test: `cd examples && GOWORK=off systemd-run --scope -q -p MemoryMax=32G go test -count=1 -v ./etcd/restart1/`
- Translation: `etc/goose.py --project restart1` (GOWORK unset).
- Build: `systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <module>`.
- Probe check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py Scratch/S7Probe.lean`.
