# auth-lease handoff (`etcd_authlease_safe`)

Plan: `notes/auth-lease-scope.md` (approved; §0, §2, §5, §7). Decisions Q1–Q9: `questions.md`,
section "auth-lease". Worktree `/shared/etcd-grove-rs56`, branch `auth-lease` (off lean `89ef103d5b`,
with `auth-lease-scope` merged).

## Done

- **S0 (probe), 2026-11-14.** Unlinked, untracked: `Scratch/AuthLeaseProbe.lean` (the apply layer's lease
  check at the latest state) and `Scratch/AuthLeaseProbeModel.lean` (the mode-`on` model on the triple
  state). Both check with no `sorry`. Findings: CP0 report (below, "Pitfalls").

- **S1 (empty-user fix), 2026-11-14** (go from etcd-grove-81): `leaseCheckFrom` over `principalBound`,
  `v3rpc.leaseCheckT` over the new `v3rpc.principalBoundT` (`infoBoundTM` deleted); lemmas
  `principalBoundOn_of_ctxBound`, `principalBound_ctx` (`LeaseCheck.lean`); ledger and decisions.md entries;
  full build passes; interfaces unchanged (`gen-interface --check` on every `etc/api` list); waiting for the
  coordinator's go to run `etc/land.sh`.
- **S2 Draft** (design text): `notes/auth-lease-s2-draft.md`, reviewed in rounds (`/shared/tmp/auth-lease/`).

- S1 landed: lean `28b89b9dd6` (2026-11-14).
- **S2 (apply layer at the latest state with a lessor), proved, 2026-11-15** (Freeze approved by
  etcd-grove-81 with the five design choices): `AuthLatest` (lease vocabulary, `isAuthStoreL`'s snapshot
  clause), `AuthApplyLatestPut` (`checkLeasePuts{,Keys}.specL`, `checkPutAuth.specL`, `Put.specL`),
  `AuthApplyLatestTxn` (`txnPutsW`, `txnOutLL`, the txn checks), `AuthApplyLatestRevoke` (new:
  `revokePreW`, `LeaseRevoke.specL`), `AuthApplyLatest` (`authOutLL`, `kvPostFL` + lease class),
  `DispatchKVL` (`authKVKind`, `kvOutL`/`kvShapedL` with leases, `applierKVL`'s revocation triple,
  `dispatch.kvSpecL` widened, the revocation branch), `ApplyKVL`/`ApplyFnKVL` widened, `UberKVLBase`,
  server: `KVOutcomeOn` (`txnPutsW_plain`, `authOutL_of_kvOutL` over `plainCover`), `ApplyNormalOn`,
  `UberOn`, `UberKit` (`LeaseRevoke.specL`), `EtcdServer__applyEntryNormal`, `Results`
  (`apply_lease_revoke_latest`). Full build green; lean `dd068e790f` merged.

- S2 landed: lean `c3da59fa29` (2026-11-15).

## Next, in order

1. S3, revised (etcd-grove-81, 2026-11-15, option (a) of `/shared/tmp/auth-lease/s3-scope-gap.md`; 26–40 days after
   S3a review r1's F1 (ii), F2 (a), F3),
   in three Freeze packages:
   - **S3a** (now): the model and the apply thread: the triple state with the lease table, the client's half kept in
     `kvInvOn`, the auth-on table for `srvRest`, `authKVKind` in the three places, admission of grants, revocations and
     leased puts at the revocable mode. Design: `notes/auth-lease-s3a-draft.md` (revision 4 = the S3a Freeze package,
     three review rounds `/shared/tmp/auth-lease/s3a-review-r{1,2,3}.md`; N1 (ii′): `leaseExactL` in the class
     track's `kvPostF`); **frozen at revision 5** (etcd-grove-81, 2026-11-15, after round 4; tag
     `auth-lease-s3a-frozen`). **Probe done** (2026-11-15): `kvOwnAt` and `kvOwn ⊣⊢ ∃ L, kvOwnAt E log L` proved
     (`Scratch/S3aProbe.lean`, untracked); `applierV3backend.Put`'s proof has the live set `L` in hand and splits
     on `o.leaseID = 0 ∨ o.leaseID ∈ L` (`applierV3backend__Put.lean:97-170`), rebuilding `kvOwn` at the same `L`
     (`kvOwn_of_split`), so its `kvPostF` conjunct is local; the key-length bound is closed by §5. **Prove: started 2026-11-15, STOPPED at a finding**
     (see "S3a Prove: where it is" below). Order (Draft §8): (1) the model (`KVAuthModel.lean`: `OnState`, `kvEntryOn`/`kvRaftOfOn` on it,
     `kvGrantedL`/`leaseGrantedM`/`leaseOk` from `Scratch/AuthLeaseProbeModel.lean`, `plainEntryOn lm`/`plainReqL`/
     `txnPlainL`, `entryDetOn`/`entryShapeOn lm`, `keysNonEmpty`, `keysLeasesLive`, `KVAuthBridge.leaseOk_iff`);
     (2) `kvInvOn` + alloc, `appliedTableM`, `srvKVInvsOn`'s rows (`lm = E.lm`, `pre = []`), `appliedTableM_eq_model`;
     (3) `kvOwnAt`/`leaseExactL`/`kvPostF`'s conjunct through backend/quota/capped/corrupt/auth, `kvPostFL`, the four
     layer triples; the apply thread's model (`outcomeOn`, `kvAppliedOn`, the S2 `plainCover` lemmas restated);
     (4) the snapshot path (§5, its frozen `hnl` text); (5) `applyEntryNormal.wp_proofOn`/`apply.wp_proofOn`, the
     examples' proofs. `KVAuthModel` rebuilds ~1500 modules: full builds under the flock.
   - **S3b**: the request side (grant, revoke, leased put with auth on).
   - **S3c**: the couplings and `NewServer`; the `lease.bootCfg` hub change and the `NewLessor` docstring (hard stops).
   - The auth-on snapshot path carries the leases (F2 (a)); the latest track gains a lease-exact outcome (F1 (ii)).
2. S4 with the client's leased put (`WithLease`, `Put`/`Txn` with a lease) and linearizable client specs of
   `Lease.Grant`/`Revoke` (F3).

## S3a Prove: where it is (2026-11-15, after rev 6)

Rev 6 (§14) FROZEN with the stronger guard (etcd-grove-81); its frozen-text edits are made (`EtcdServer.{Put,
DeleteRange}.spec`, `txnAppliedOk`, v3rpc `putApplied`/`deleteApplied`/`txnAppliedAns`, client `KVService` rows,
`readQ_of_ansM`, `srvKVCoreM_fire` + `srvKVFacts_fire(0)`, `kvLogOkTo`). The tree does NOT build yet.

**Strategy: a transitional port first.** `srvKVInvsOn` keeps a TRANSITIONAL `γr.kv.lg = false` (beside the frozen
`lm = E.lm ∧ pre = []`); the apply and snapshot proofs take `lm = none` from it (`KVNames.lm_of_lg_false
Hrows.2.2.1`, marked "TRANSITIONAL until the §5 step") and keep their `plainCover` reasoning. Steps 3 (§3a
`leaseExactL`/`kvOwnAt`/Chain's `kvPostF`), 4 (§5, drop the transitional row) and 5 (revocable-mode apply arms) come
after the tree builds.

Checked clean with `etc/lean-check.py` (in order): KVAuthModel, KVApplyOn, KVModelM, KVReadOn, KVAuthShape, ProposeOn,
ServerOnDefs, ImageOn, ServerOn, NewServerAllocOn, AuthTie, AuthTieRead, ReqOn, ReadOn, auth/Hist, KVOutcomeOn,
ApplyEntryOn, ApplyTieOn, ApplyNormalOn, SnapRecvOn, MergedImageOn, SnapAuthRecover, AuthCompRows,
Spec/EtcdServer__applyAll, ApplyAllSnap, ModeSpecs, EtcdServer__Range, EtcdServer__apply, EtcdServer__applyEntryNormal,
StartOn, RunOn, NewServer, EtcdServer__applySnapshot (SnapApplyPost), SnapSendBranch, StopShutdown, EtcdServer__run,
ClientModel, EtcdServer__Put/DeleteRange/Txn. Edited, not yet checked: auth/MainAlloc, etcdstart/Alloc3On (alloc premises),
server Results (`server_member_alloc_on` premises), KVLogOk, client WatchFire/Results/KVService, v3rpc ServerKV, InvRead.

Next, in order: server Results, v3rpc ServerKVOn/Results, the client chain (KVService, ServerKVPut/Get/Txn, ClientPutGet,
Results, ResultsOn, KVServiceOn, WatchFire users, kubernetes), examples (auth, auth3, etcdstart, restart1, watch, k8s,
txnlin, partition). Then a full build (flock, 64G) to find the rest.

Tools: `/shared/tmp/auth-lease-s3a/chk.sh FILE...` (lean-check in order, stops at the first file with errors;
`LINES_SHOW=N`); `/shared/tmp/auth-lease-s3a/hg.py` (adds `kvInvOn`'s `HG` conjunct to open/close patterns).
Lemmas added for the port: `kvLeasesOn_none`, `kvRaftOfOn_table_none`, `kvTable_plainOn_none`, `kvRaftOfOn_conf`,
`kvLeasesOn_conf`, `leaseGrantedM_of_plainCover`, `kvGrantIds_snoc_keep`, `entryRevGrantId_nonGrant`; `kvAppliedM true`
is `kvAppliedOn … (kvLeasesOn γk st₀ A)`.

## Pitfalls

- `kvStOn` is `@[reducible]` but `rw` does not see through it: write `kvStateOf (kvModelOn …) (kvLeasesOn …)`
  in goals that are rewritten.
- With `apply.DispatchKVL` imported, `and_false` can be ambiguous in `simp only` (`BI.and_false`): use
  `_root_.and_false`.

- The latest-state refusal must be stated in `refusedL`'s form (`leaseRefusedL`), not `¬ leasePassedL`:
  `latestOk` is vacuous at `hs = []` and in mode `any`.
- `isAuthStoreL`'s admin clause gives only the latest verdict; the lease class (`leaseKeysClass`'s
  admin disjunct) needs a recorded state: the probe adds `□ ∀ hs, L hs -∗ L hs ∗ auth.latestSnap M hs`
  (real store: `latestResC_snap`).
- The model's refusal guard `isKVKind` excludes `.leaseRevoke`: the triple-state model's guard must
  add it (`authKVKind`), or a refused revocation is applied.
- `txn.putsW`, `lease.keysOf`, `kvGrantedPerm` (Scope Draft names) do not exist; the probe defines
  `putsW` (mutual `opPuts`/`opsPuts`) and states key sets over `I.lookup ⟨k⟩ = some id`.

## Build

Targeted: `systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
<modules>`; check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py FILE`. Full builds
under `flock /shared/tmp/etcd-grove-build.lock`. `TMPDIR=/shared/tmp`.

## Left (follow-ups)

- **The empty-prefix fact ties the auth-on server to fresh starts** (S3a rev 5, `srvKVInvsOn`'s `γr.raft.pre = []`):
  an auth-on restart (future work) has to revisit it (the model's table folds over the applied entries, `srvRest`'s
  over the raft prefix and them).
- A revocable auth-on cluster's snapshots: carried by S3a §5 (the image's table, `keysLeasesLive`).
