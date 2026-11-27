# WatchOn_dist: the auth-on cross-machine watch with the auth row (2026-11-26)

Branch `etcd-safe-watchon/2026-11-26` off `etcd-safe-full/2026-11-26` @ `ac82116815`. For the full
`etcd_safe_nocrash`'s auth workload (`RunAuth`, `examples/etcd/dist/client/auth.go`; the principals' `auth.Work`):
root's watch (events, complete from 1), u's watch of `[a, b)` (events), and each principal's refused watch of
`c/` (no response with events), which `Watch_dist` cannot give (its row was dropped, `notes/etcd-dist-plan.md`
§22.5 item 2, deferred to N11 = F7's `Γ.au`). One interim axiom, new files only; no Go change, no `sorry`, no new
top-level premise. **Held: nothing lands before Upamanyu's F9 approval.**

## Files

- `Proof/.../etcd/dist/WatchOnViewDist.lean` (defs): `outTokOkS P om` (F7's `outTokOk` of every metadata with
  `om`'s stream key: the watcher shares one stream per key, and the key collides), `outTokOkS_none` (proved),
  `watchFloorsD eps Γ γR L₀` (at each endpoint, `∃ mid m, etcdAddrAt a Γ mid ∗ authFloorD Γ γR mid L₀ m`),
  `watchCheckedD eps Γ γR P L₀ key rangeEnd` (`∃ mid info L, servedBy eps Γ mid ∗ srvReqLogLb γR L ∗
  ⌜userOk P info.Username' ∧ L₀ <+: L ∧ auth.permitted (srvAuthAtLog Γ.kv srvAuthSt0 L) (authInfoM info)
  (watchKey key) rangeEnd .read⌝`).
- `Spec/.../etcd/dist/WatchOnDist.lean`: `WatchOn_dist.spec` = `Watch_dist.spec` with `cfg`, `γR`, `L₀`;
  premises `∀ a b, Γ.au a = Γ.au b → a = b`, `Γ.auth = true`, `γR.raft.log = Γ.kv.rlog`,
  `outTokOkS (principalOf cfg) om`; pre adds `clientF cl "cfg" ↦□ cfg ∗ ⌜cfg.Token' = []⌝ ∗ watchFloorsD eps Γ γR
  L₀`; the elements' row slot `watchCheckedD … (opWatchModel key opts).key (opWatchModel key opts).base.rangeEnd`.
- `Proof/.../etcd/dist/WatchOnDist.lean`: `axiom WatchOn_dist.wp_proof`.
- `etc/dist-axiom-diff-allow.txt`: its `pair` line against `watcher.Watch.spec`, 23 `dev` lines with reasons.

## Route table row

| Route | Why not now |
|---|---|
| Translate and prove | Translated and proved in one process (`watcher.Watch.spec`, row `watchCheckOk`); across machines the stream needs `etcdSvc Γ mid`'s `Watch` entry, not statable before S2's etcd-side stream work (§22.6) |
| Go model | the grpc model itself: the same gap |
| Trusted stand-in | would trust the reconnection logic the single-process proof verifies |
| Retirement | `Watch_dist`'s route (a): the `Watch` entry at `Γ` (SW1's `.stream` entries), `watcher.Watch.spec` over the table's `isClientWatcher`, the row from `watchCheckOk` at `Γ.au mid` plus `authFloorD`'s update (F7's R1) and `attemptTokOk`/`outTokOkS` for the user |

## What RunAuth uses

The floors: each barrier (`KV_GetOn_dist` at one endpoint) gives `readCheckedD`'s `authFloorD` at its member,
with the set-up's prefix as `L₀`. root and u: `om = none` (`outTokOkS_none`). The principals: `none`, or the
anonymous `bad` with `token=badtoken` (`outTokOkS` from a one-entry variant of `streamKeyOf_single`: the colliding
metadata has the one key, so no `authorization`, and `badtoken` has no `tokShape`). The refusal: `watchCheckedD`
at a state after `L ⊒ L₀` is the frozen set-up state (the cluster-level `akAuthFixed`), where no principal reads
`c/` (`not_granted_c`).

## Review (`notes/axiom-review/watchon-dist.md`; Go test `notes/axiom-review/watchon-dist/`)

SOUND WITH FIXES, statement unchanged. F1 (collision example), F2 (snapshot `Recover` interleaving), F3 (the
floor is the serving member's) applied to the docstrings. Deferred to the adoption commit (trusted docstrings of
other axioms):
- **F4**: `WatchDist.lean`, `Watch_dist.wp_proof`'s "*Any auth mode.*" bullet, stale since F7 step 3; the
  review's replacement text is in its §7.
- **F5**: `ServeDist.lean`'s docstring names `WatchOn_dist`'s streams (review §7), with N3's F4 (on
  `etcd-safe-f5`).

Etcd behaviour the test measured (not a hole in this deployment; the floors exclude it): a member lagging across
`AuthEnable` passes anonymous watch creates at its old auth state, and such a watch keeps streaming events written
after the enable (Go test [lag]: 2 of 13,556 creates).
