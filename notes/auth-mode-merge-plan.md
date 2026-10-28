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
   `kvSpecL` 20, `specSure` 8. A separate, larger stage; plan it after steps 1-5.
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
