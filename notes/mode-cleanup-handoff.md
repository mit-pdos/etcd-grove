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

## Not merged, and why (checkpoint 1, for etcd-grove-81)

- **The five admin `specOn`/`wp_proofOn` (AuthEnable, UserAdd, RoleAdd, UserGrantRole,
  RoleGrantPermission; 10 twin findings).** `spec` is already mode-free (a contract `authRaftOk` passed
  through); `specOn` is its instance at `authRaftOk_on` (auth on), proved from `wp_proof` (no second proof
  of the code). No mode-indexed statement exists: with auth off an admin request is outside the KV model
  (`reqPropOk` admits KV requests only), so a merged form would say less than `spec` or add a case that is
  false. They are corollaries; option: move them to `ModeSpecs.lean` (names and texts unchanged, the
  exported `server_*_on` unchanged). Not done: it lowers the count by relocation, which the brief forbids
  without a decision.
- **`NewServer.specM`/`wp_proofM` (2).** `specM on = specG on false`; `spec = ∀ cmp, specG false cmp`. A
  merged `∀ on cmp, specG on cmp` linked once would put the auth-on construction's premises
  (`authSrvTP`, `uberKitM`, D22's trusted `authSchemaSrv`, which `server_new_auth_on` takes as `hD22`) on
  `wp_NewServer` and every auth-off closed theorem. Changes what they say: left.
- **`apply.wp_proofOn`, `applyEntryNormal.wp_proofOn` (2).** One spec each already (`ModeSpecs` has the
  corollaries); the twins are second proofs. `apply`'s off/on proofs are ~1000 lines each, 334 differing
  lines, over ~25 lemma pairs (`srvApplyKV_writer`/`srvApplyKVOn_writer`, `kv_applied_step`/`_on`,
  `kvApplied_next`/`On`, `srvRestR*`/`srvRestRM*`, `waitInv`/`waitInvM`, …; the off proof's KV model is
  over the log, the on proof's over the triple state). Merging = M-forms of those lemmas first, then one
  proof over `E.authOn`; `applyEntryNormal`'s on proof also has the admin arms (600 vs 1100 lines).
  Estimate 1–2 weeks for `apply` alone; proposed as its own stage.
- **client/v3 `kv.{Do,Put,Get,Delete}.specM`, `txn.Commit.specM` (5).** Not auth-mode twins: `M` is the
  members (D44: a `*kv` of the members `ms`, `isKV`; `spec` is one KV, `isKv`). Nothing to merge; the gate's
  name pattern catches them. Options: a `members` class in `etc/mode-allow.txt`, or a rename (changes
  `LinkMembers`'s linked statements' names).
- **C5′ pair (`lessorGrantOkG`/`lessorGrantOk`/`lessorRevokeOk`/`raftLessor` beside the `…M` forms).**
  Merging changes either the seven exported client results' texts (`raftLessor s E S` →
  `raftLessorM false s E ρ S`, +7 lit-mode) or the bodies of the four definitions they are written in
  (to the `…M` form at `false`; equivalent by the `_false` laws, not by `rfl`). Both change exported
  text: needs a decision. The pair is not counted by the gate.
- **The `unmoved` match-mode and lit-mode findings in definitions** (`isServerBuiltM`/`isServerBuiltOn`,
  `applyBuiltOn`, `isServerReqM`'s `srvReqFieldsAtM`, the `…On` aliases): reached by exported results
  (fingerprint: e.g. `server_built_gap_on` states `isServerBuiltM`); a uniform body changes their text.
  The lemma findings (`reqPropOkM_true_*`, `LeaseReqOn`'s, `grantedAt_of_*`, …) are auth-on facts (the
  `true` forms of `reqPropOkM`, `modelOutM`, `kvModelOn`): not true at both modes as stated.

## Next, in order

1. etcd-grove-81's decisions on the items above.
2. If the admin corollaries may move: move them to `ModeSpecs.lean` (import check: `ModeSpecs` must
   import `AdminOn` and the five Spec files; no cycle with `Results`).
3. If definition bodies under exported results may change when proved equivalent at each mode: the
   `…M` rows with a `match` (`isServerBuiltM`, …) one by one, each with `X_false`/`X_true` kept as
   propositional laws.

## Build and checks

- Full: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
  --packages=/shared/tmp/manifest-ddc.json build` (an `AppliedIndex` spec change rebuilds ~914 modules).
- Fingerprint baseline at lean: `/shared/tmp/mode-cleanup/fp-base.txt`
  (`LAKE_OPTS=--packages=… .claude/skills/proof-perf/fingerprint.py -o …`, `--diff`).
- `etc/mode-check.py --check [--update]`, `etc/tcb-report.py --check`, `etc/bounds-check.py --check`,
  `etc/gen-interface.py etc/api/<pkg>.txt --check`.
