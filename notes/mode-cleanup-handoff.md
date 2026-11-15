# Mode-divergence cleanup: handoff

Stage between auth-on-leases S3c and S4 (user-approved 2026-11-15, via etcd-grove-81). Branch `mode-cleanup`
off lean `9cf04e8ec0`, worktree `/shared/etcd-grove-rs56`. Goal: lower `etc/mode-check.py`'s counts by real
merging (twins into mode-indexed specs, auth-on-only lemmas over the slot, S3c's C5′ pair), no closed
statement changed, trust base 870/4, no trusted text.

## Done

- **Batch 1: `EtcdServer.AppliedIndex`** — `specM on` merged into `spec` (`spec := ∀ on s E γr, …`, the
  same triple; `wp_proofM` folded into `wp_proof`); callers `isReadServer_of_serverM` (takes `spec`, applies
  it at its `on`) and `start`'s proof. Twins etcdserver 16 → 14. No exported statement changed (`spec`
  unfolds to the same proposition; `server_*` results name `spec` only).

- **Batch 2: the five admin `specOn` corollaries moved into `ModeSpecs.lean`** (decided by etcd-grove-81,
  2026-11-15, item 1): `EtcdServer.{AuthEnable,UserAdd,RoleAdd,UserGrantRole,RoleGrantPermission}.specOn`
  (texts unchanged) and their proofs as `X.spec_on (h : X.spec) (hRR : raftRequest.spec) : X.specOn` (until
  then `wp_proofOn` in the proof files, proved from `wp_proof`; UserAdd's `bcrypt` premise now through `h`);
  the exported `server_*_on` keep their statements (`X.spec_on EtcdServer.wp_X server_raft_request`).
  `AdminOn.lean` no longer imports `ModeSpecs` (it used nothing of it; `SDRun` in its place), so `ModeSpecs`
  can import the five Spec files. Twins etcdserver 14 → 4.
- **`members` class** (item 2): client/v3's `kv.*.specM`/`txn.Commit.specM` (D44) classified `members` in
  `etc/mode-allow.txt` (new class in `etc/mode-check.py`); count unchanged (5).

## Not merged, and why

- **`NewServer.specM`/`wp_proofM` (2)** — left (decided by etcd-grove-81, item 3). A merged
  `∀ on cmp, specG on cmp` linked once would put the auth-on construction's premises (`authSrvTP`,
  `uberKitM`, D22's trusted `authSchemaSrv`, `server_new_auth_on`'s `hD22`) on `wp_NewServer` and every
  auth-off closed theorem.
- **`apply.wp_proofOn`, `applyEntryNormal.wp_proofOn` (2): a proposed stage of its own, 1–2 weeks**
  (item 4, to be scheduled by etcd-grove-81). One spec each already; the twins are second proofs.
  `apply`'s off/on proofs are ~1000 lines each, 334 differing lines, over ~25 lemma pairs
  (`srvApplyKV_writer`/`srvApplyKVOn_writer`, `kv_applied_step`/`_on`, `kvApplied_next`/`On`,
  `srvRestR*`/`srvRestRM*`, `waitInv`/`waitInvM`, …: the off KV model over the log, the on one over the
  triple state). Plan: M-forms of the lemma pairs, then one proof over `E.authOn`; `applyEntryNormal`'s on
  proof also has the admin arms (600 vs 1100 lines) and holds 29 of the remaining unmoved lit-mode
  findings; `applyAll.wp_proofSnapM`/`snapRecv_imageR`/`snapRecv_imageOnR` (8 more) are the same kind.
- **`isServerBuiltM` (item 5, studied, not done).** Its two bodies differ beyond the mode-indexed rows:
  `applyBuilt`/`applyBuiltOn` hold `srvAuthApplyRes` vs `srvAuthApplyResB … srvAuthSt0` (the latter with
  the backend tie and the write lens), `srvUberBase` on only, `kvRun` vs `kvRunOn` (with `∃ st`, not
  `kvRunM`'s `st`), `srvTokRights` on only (keyed on `E.authMode`, so not `True` at `on = false` without a
  premise). A uniform body needs new mode rows (`srvAuthApplyResM`, a match; an `on`-guarded
  `srvTokRights`, `srvUberRowM`), so the match moves rather than goes: net −1 match / −5 lit at best,
  +1 match, and the `rfl` laws `isServerBuiltM_false/_true` (11 uses) become `⊣⊢` laws with a premise on
  `E.authMode`, with 20 `isServerBuiltOn` uses in `start`, `AuthCompRows`, `AppliedOn` and the closed
  examples' proofs to redo. Judged not worth it in this stage.
- **C5′ pair (`lessorGrantOkG`/`lessorGrantOk`/`lessorRevokeOk`/`raftLessor` beside the `…M`)** — studied,
  not done. Defining the old four from the `…M` at `false` needs a `ReqNames` the old contracts do not have
  (`∀ ρ`, whose discharge goes back through the `_false` laws: circular), and replacing them at their uses
  changes the seven exported client results' texts (+7 lit-mode). Not counted by the gate either way; the
  S3c Draft's own plan (§7.1) merges it when S4 reworks the client results: recommended there.
- **The remaining definition findings** (`isServerReqM`'s `srvReqFieldsAtM`, the `…On` aliases in v3rpc,
  `memberUpOn`, `Authenticate.spec`, …) are in exported or closed texts, or rows whose two modes are
  different models; the lemma findings (`reqPropOkM_true_*`, `LeaseReqOn`'s, `grantedAt_of_*`, `ReadOn`'s)
  are auth-on facts, not true at both modes as stated. `NewServer.specR`/`wp_proofRG`/`srvIndices_allocR`
  (14) are the frozen restart, scoped to auth off.

## Next

1. The proposed `apply`/`applyEntryNormal` proof-merge stage (above).
2. The C5′ pair with S4.

## Build and checks

- Full: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
  --packages=/shared/tmp/manifest-ddc.json build` (an `AppliedIndex` spec change rebuilds ~914 modules).
- Fingerprint baseline at lean: `/shared/tmp/mode-cleanup/fp-base.txt`
  (`LAKE_OPTS=--packages=… .claude/skills/proof-perf/fingerprint.py -o …`, `--diff`).
- `etc/mode-check.py --check [--update]`, `etc/tcb-report.py --check`, `etc/bounds-check.py --check`,
  `etc/gen-interface.py etc/api/<pkg>.txt --check`.
