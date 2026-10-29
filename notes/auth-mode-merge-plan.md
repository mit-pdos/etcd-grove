# Plan: one server spec for both auth modes (merging the `spec`/`specOn` pairs)

**Status.** Planned (2026-10-28), not started. A handoff to whoever owns the auth server side
(the auth plan's E stage, `notes/auth-plan.md`), to run **after `auth-e3zc` lands** and timed
against M2 (below). Nothing here has been built; the counts are from `lean` at `10e2918d3e`.

## Why

The E stage restated the server, layer by layer, in the auth mode `on` beside the mode `off`
(since E2p found the mode-`on` statement vacuous: `kvInv` fixed the auth layer off). There are now
19 `EtcdServer.*.specOn` beside their `spec`, each with its own proof. That is what the `spec`
skill's principle forbids (`.claude/skills/spec/PRINCIPLES.md`, "One general spec; special cases are
instances": "auth on and off as two specs ... a mode is part of the state. Two mode variants are at
most a development hack to put off merge conflicts"). The cost is concrete: every change another
track makes to the server's invariants (D22, raft's node API, C1's `srvTokRights`, M2) has to be
made in both copies; `auth-e3zc` is doing that now on the apply loop.

The precedent to follow is already in the tree: `EtcdServer.raftRequest.wp_proofM (on : Bool)` is
the one proof, and `wp_proof` (the mode `off`) is derived from it through `isServerReqM_false` and
`reqPropOkM_of_false` (`EtcdServer__raftRequest.lean:268`). `NewServer.specM`, `doSerialize`,
`AppliedIndex`, `getAppliedIndex`, `setAppliedIndex`, `setTerm`, `parseProposeCtxErr`,
`processInternalRaftRequestOnce` have `specM (on : Bool)` too.

## The pairs

Similarity: of the two proofs' tactic lines, whitespace-normalized (`difflib` ratio).

| group | functions | `wp_proof` / `wp_proofOn` lines, similarity | verdict |
|---|---|---|---|
| already instances | `AuthEnable`, `UserAdd`, `RoleAdd`, `UserGrantRole`, `RoleGrantPermission` | `wp_proofOn` 15-26 lines, applies `wp_proof` at `authRaftOk_on` | nothing to do (the right pattern: the general spec is parametric in `P`/`Q`) |
| apply loop, mechanical | `snapshotIfNeededAndCompactRaftLog` (80/79, 0.95), `applyEntries` (201/201, 0.96), `applyAll` (198/197, 0.92), `run` (519/518, 0.95), `apply` (762/784, 0.92) | | **merge first** |
| start, mechanical | `start` (498/526, 0.87), `Start` (144/144, 0.84) | | merge after the apply loop |
| request path | `Put` (173/180, 0.89), `DeleteRange` (169/189, 0.87), `Range` (258/287, 0.88) | | merge; the `M` vocabulary mostly exists |
| different structure | `applyEntryNormal` (483/529, 0.49), `Txn` (408 / `On` 290 + `OnR` 290, 0.67) | | last; needs the apply layer's families first |

The callers outside the server (`api/v3rpc/ServerKVOn.lean`'s `*_of_serverOn`, `run_job_bodyOn`,
`Results.lean`'s `server_*_on`, `examples/authkv/startServer.lean`) follow their callee.

## How much duplication there is, by track (measured 2026-10-29)

Over the server's and raft's proofs (`Proof/go_etcd_io/etcd/server`, `Proof/go_etcd_io/raft`: about
10,000 theorems, 240k non-blank lines), on `lean` at `d56ff440c6` and on `m2` at `4710a15628`. A
theorem of at least 25 lines counts as a copy when at least half of its 4-line blocks
(whitespace-normalized, comments dropped) reappear in another theorem; the lines counted are the
shared part. Copies that were rewritten are missed, so these are lower bounds. Definitions are
counted by name suffix.

Copied proofs, about 10.5k lines (4.4%):

| source | copied lines | what |
|---|---|---|
| auth, on/off copies | ~3.5k (33 pairs) | `apply` 595, `run` 414, `start` 350, `Txn`, `Range`, `applyEntries`, `applyAll`, `DeleteRange`, `Put`, `Start`, `NewServer`, `srvClusterBoot_alloc`/`…On_alloc`, `ServerKV`/`ServerKVOn` |
| auth, other variant families | ~1.6k (14 pairs) | `auth.authStore.UserAdd` proved three times (`wp_tie`, `wp_sure`, `wp_tieSureB`, ~270 lines each); `uberApplier.dispatch.wp_kvL`, `apply.Apply.wp_kvL`/`wp_adminL`, `wp_latest`, `wp_lb` |
| raft | ~1.3k sibling, ~0.2k variant | `raft__Step/Msg*` handlers over similar Go; `RawNode.Step` against `wp_rn_raft_Step_net`, `ownRaftPhysCV`/`CVW` |
| similar Go functions elsewhere | ~3.5k | the `EtcdServer` admin wrappers (~63 lines each), `requireAuthInfo` in `etcdserver` and `v3rpc`, lessor `Attach`/`Detach`, the `kvServer` handlers |
| snapshots (D22) | ~40 | folded into the main specs (one `specSnap`) |
| compaction (M2, mvcc) | ~100 | mvcc's `Scheduled`/`Finished` setters (similar Go); `m2` adds no copied proof |

Parallel definitions and statements:

| family | definitions | lines |
|---|---|---|
| auth on/off (`…On`, `specOn`) | 82 (56 with an off twin) | ~790 |
| auth latest/tie/fuel/lb/sure (`specL`, `specT*`, `fuelSpec*`, `specLb`, `specSure`) | 63 | ~785 |
| compaction (`specR`, `…Cmp`) | 20 | ~310 |
| snapshots (`…Snap`) | 15 (1 with a twin) | ~150 |

Compaction's `specR` (`storage/mvcc/ReaderSpecs.lean`) are instances, each with a corollary
`spec_R : spec → specR` and no second proof: the pattern this plan wants.

So about 7k lines (proofs and definitions) are duplication a track introduced, almost all of it
auth's; snapshots and compaction kept one spec per function. Steps 1-5 below remove the ~3.5k of
on/off copies; the ~1.6k of other variants is step 6. The raft and sibling-function duplication
follows the Go code: lemmas shared between siblings could shrink it, but no track has to port a
change into two copies of it.

## What the mechanical diffs are

Every `spec`/`specOn` diff in the apply loop and start is the same substitutions:

| `spec` (off) | `specOn` | `M` form | `_false` lemma |
|---|---|---|---|
| `isServer` | `isServerM true` | `isServerM` (`AppliedOn.lean:231`) | `isServerM_false` |
| `isServerReq`, `isServerRead` | `…M true` | exist (`ReqOn`, `ReadOn`) | exist |
| `isServerBuilt` | `isServerBuiltOn` | `isServerBuiltM` (`StartOn.lean:122`) | `isServerBuiltM_false` |
| `logShape` | `logShapeOn` | `logShapeM` (`ServerOn.lean:57`) | check |
| `srvApplyKV s E γw x` | `srvApplyKVOn s E γw x sa` | **missing** | |
| `kvApplied γ γk A x` | `kvAppliedOn γ γk srvAuthSt0 A x sa` | **missing** | |
| `entryOk` | `entryOkOn` | **missing** | |
| `isServerRun` | `isServerRunOn` | **missing** | |
| — | premises `E.authMode = .on γa`, `receiptBound GF ≤ 2^48`, `srvLessorNil s`, `⧗ 1` | gate by the mode | |
| — | post `srvAuthLb s E`, `pubAfterM`, `hdrBoundM`, `grantedAt` | `pubAfterM`/`hdrBoundM` are `True` off; `srvAuthLb`, `grantedAt` to gate | |

The auth state `sa` is an extra binder in `On`; in the merged spec it is bound in both modes and
unconstrained (or fixed to `srvAuthSt0`) off.

## The steps

0. **Before starting**: `auth-e3zc` merged; ask the user where M2 stands (below). Work in a
   worktree on its own branch.
1. **The missing `M` predicates**: `srvApplyKVM`, `kvAppliedM`, `entryOkM`, `isServerRunM`, each a
   `match on` with a `_false` lemma by `rfl` to the off predicate (as `isServerReqM`), and the gated
   premises (`srvLessorNil` and `receiptBound` only on; check whether off can simply take them:
   `srvLessorNil` holds of every server the examples build?).
2. **The mode as the state, not a flag.** Index by the environment's mode (`E.authMode.isOn`)
   rather than a free `Bool`, so the merged spec has no mode parameter; the `on` premise
   `E.authMode = .on γa` becomes the definition. Decide this with the spec reviewer before step 3:
   it is the difference between `specM on` everywhere (today's precedent) and one `spec`.
3. **The apply loop, bottom-up**: `snapshotIfNeededAndCompactRaftLog`, `apply`, `applyEntries`,
   `applyAll`, `run`. Each: one `wp_proofM` (the `On` proof generalized, case-splitting only where
   the two differ), `spec` and `specOn` as its instances (or replaced, per step 2), callers updated.
   **The bridge**, so a caller need not wait for a hard callee: `X.specM m := match m with | false
   => X.spec | true => X.specOn`. `apply` takes `applyEntryNormal.specM m` this way until step 6
   merges it; the bridge is then deleted.
4. **Start**: `start`, `Start` (and `examples/authkv/startServer.lean`).
5. **The request path**: `Put`, `DeleteRange`, `Range`. One spec decision: `putPermitOn` requires a
   non-empty key. Either `⌜on → key ≠ []⌝`, or the off spec requires it too (the gRPC layer refuses
   an empty key, `ErrGRPCEmptyKey`, so every gRPC caller has it; check the non-gRPC callers:
   `examples/` that call the server directly). `ServerKVOn.lean`'s `*_of_serverOn` merge with
   their off versions.
6. **`applyEntryNormal`, `Txn`**: their `On` proofs consume the apply layer's other families
   (`apply.Apply.kvSpecL`, `authApplierV3.*.specL`, `applierV3backend.*.fuelSpecX`,
   `CheckTxnAuth.specLb`, `adminEntryOn.spec`), and `Txn` splits into `specOn`/`specOnR`. First
   decide which of those families are modes (merge) and which are different specs (keep):
   reference counts on `lean` are `specL` 99, `specT` 65, `specLb` 57, `fuelSpecX` 55, `specTB` 27,
   `kvSpecL` 20, `specSure` 8. A separate, larger stage; plan it after steps 1-5. Its cheapest
   item, which need not wait: `auth.authStore.UserAdd`'s three proofs (`wp_tie`, `wp_sure`,
   `wp_tieSureB`, ~800 lines, `auth/authStore__UserAdd*.lean`), probably one proof of the
   strongest (`tieSureB`) and two short corollaries.
7. After each step: `lake build`, `etc/tcb-report.py --check` (the trust base must not move),
   `etc/gen-link.py --server --check`, the interfaces (`etc/gen-interface.py`), and the spec
   reviewer on the merged specs (`spec` skill: a merged spec is a changed spec).

Rough size: steps 1-5 remove about 4.5k lines of duplicated proof (the second copies in the
mechanical and request groups).

## Coordination

- **`auth-e3zc`** (C1, `/shared/etcd-grove-e3zc`) edits the apply loop's specs (`srvTokRights` in
  `apply`, `applyEntries`, `applyAll`, `applyEntryNormal`) and the `On` vocabulary (`ApplyNormalOn`,
  `ApplyTieOn`, `UberOn`, `AuthSrv`, `AdminEntryOn`). Do not run concurrently with it; start when it
  has landed, ideally as the auth track's own next stage.
- **M2** (`m2`, `/shared/etcd-grove-cp`, paused until `backend-cmp`): 17 commits, 145 files ahead of
  `lean`, including the whole apply loop (`applyAll`, `run`, `start`, `applyEntryNormal`,
  `AppliedOn`, `ApplyNormalOn`, `KVAuthModel`). Land this plan's steps 1-5 **before M2 resumes**
  (M2 then rebases once onto one spec) or **after M2 lands**; not interleaved.
- **`backend-cmp`** (`/shared/etcd-grove-be`): in `storage/mvcc` and `storage/backend`; its
  server-side touches (`hookStep`, the put/`UnsafeDelete` premises, `srvWTPool`) are invariant and
  hook files, not these specs. Little overlap.

## Progress (branch `auth-mm`, worktree `/shared/etcd-grove-amm`, started 2026-10-29)

**Step 0.** `auth-e3zc` (C1's A1-A3) merged into `lean` (`0bb0334b84`); M2 paused behind
`backend-cmp` (the user's order, relayed 2026-10-29).

**Step 1 done** (internal predicates; decided by the agent): `srvApplyKVM`, `kvAppliedM`
(`AppliedOn.lean`), `srvLessorNilM` (`UberOn.lean`), `entryOkM` (`ApplyNormalOn.lean`),
`isServerRunM` (`RunOn.lean`), each a `match on` with `_false`/`_true` lemmas by `rfl`.

**Step 2, the spec review** (`spec-reviewer`, 2026-10-29) of two candidates on `applyAll`: (A) a
`Bool` parameter, today's `specM on`; (B) no parameter, the mode the environment's. It
recommends B, amended:
- B as drafted claimed the mode-`on` spec at `.any` (`AuthMode.any.isOn = true`), which no proof
  covers: exclude it (`E.authMode ≠ .any`);
- the flag is `E.authOn`, and a postcondition row about `E'` uses `E'.authOn`;
- the premises only `on` needs (`srvLessorNil`, `receiptBound ≤ 2^48`, `Put`'s non-empty key)
  stay gated by the mode.

Its findings:
- B's premise `E.authOn = false` on today's off spec costs nothing: the off precondition is
  contradictory at `E.authOn = true` (`kvInv_ch0_off`, `applyKV_authOn`), and every off client
  builds `.off`.
- A's corollary `spec := specM false` fails at an `.on` environment (`srvTokRights` is a real
  resource there).
- A keeps the exported results split (`server_*`/`server_*_on`).

Decided by the agent:
- the gating of the `on`-only premises (the reviewer's "no unneeded premise"; it leaves the
  off statements' premises as they are);
- `sa` bound and unconstrained off.

For the user (a top-level and structural choice, "Who decides"): A or B; under B, the nine
existing `specM (on : Bool)` converted in this stage, and the exported results' pairs merged.

**Step 2 decided by the user (2026-10-29):** B, as amended by the reviewer: one spec per function
with no mode parameter, the mode `E.authOn` (`.any` excluded); the nine `specM (on : Bool)`
converted in this stage; each pair of exported results (`server_*`/`server_*_on`, v3rpc's
`*_of_server`/`*_of_serverOn`) merged into one.
