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

**Where it is (2026-11-15, session 2):** the full build is GREEN at `build9` (`/shared/tmp/auth-lease-s3a/build9.log`,
flock + 64G, commit after `auth-lease S3a §3a`); `etc/tcb-report.py --check` at 870 axioms, 4 sorries (run at `build8`,
before §3a; §3a adds no axiom). Done this session:
1. **The read rows' guard** (handoff item 1, decided by etcd-grove-81): `⌜on = true → γr.kv.lm = .none → kvLeasesOn γr.kv
   srvAuthSt0 L = []⌝` inside the `∃ L` of `rangeAnsOkM`/`txnReadAnsM` (`ServerKV.lean`), proved in `ServerKVOn` by
   `ReadOn.depQ_leases_none` (from `srvKVCoreM_leases_none`: `kv_log_plain_on` + `kvLeasesOn_none`; `iapply wp_fupd` before
   the `wp_apply` so the post can be updated). `readQ_of_ansM` (client Results) takes the guard;
   `rangeErrReply_of_errAt` became a fupd lemma over `srvKVCoreM E.authOn` (the error row `rangeErrAt` keeps its text).
   §14's table has the two rows.
2. **Client chain and examples** destructure the table (`ServerKVGet`, `ServerKVTxn`, `ClientPutGet`, `kubernetes/Defs`,
   k8s `etcd3/Compact`, `partition/WatchWrites`, `txnlin/Calls`, `auth/WorkCalls`). Pitfall: `simp only [hs, …]` on an
   Iris goal rewrites the context too: specialize `Himp $$ %hs` BEFORE the simp.
3. **§3a**: `apply.leaseExactL`, `leaseExactL_rejected`, `leaseExactL_other`, `kvOwnAt`, `kvOwn_iff_at`, `kvOwn_of_at(P)`,
   `kvOwn_atP`, `kvOwn_rejected`, `kvOwnAt_ltHalf` (Chain); `kvOwnAt_of_split`, `wSt_ne_false` (WriteLemmas). `kvPostF` and
   `kvPostFL` carry `∃ L, ⌜leaseExactL L rq log oc⌝ ∗ kvOwnAt E (oc.logAfter log) L`; the backend's Put (a dead lease's
   commit refuted by two writer halves), Txn (`txn.Txn.spec`'s `PathsLeaseOk`/rejection), DeleteRange (trivial) prove it;
   quota/capped/corrupt/auth pass it or reject (`kvOwn_rejected`); the class-track consumers (`apply/Results`,
   `uberApplier__dispatch`) forget it (`kvOwn_of_atP`). The latest track: `dispatch.kvSpecL` gains `⌜v3 = true → E.lg =
   true → leaseExactL T rq log o⌝` (from `kvOwnAt_ltHalf` at the caller's `ltHalf E T`), `uberApplier.Apply.kvSpecL`,
   `uberKVC`, `apply.Apply.kvSpecL` gain `⌜∀ o b, out = .dispatched o b → v3 = true → E.lg = true → leaseExactL T rq x.log
   o⌝`; `auth_pass_kvPostFL_nil` takes `dispatchKind rq = .leaseRevoke`. The server (`applyEntryNormal`) drops the new
   conjunct for now (`%HXo, -, #Hdel`): §6 consumes it.
4. **§4 started**: `appliedTableM`, `appliedTableM_false/true`, `appliedTableM_eq_model` in `KVModelM.lean` (checked with
   lean-check, not yet in a full build; it rebuilds ~1270 modules). **Finding:** `srvRest` (`InvRest.lean`) is imported
   by `KVAuthModel`, so it cannot read `kvLeasesOn`. Proposed form (to do): split `srvRest` into a table-generic
   `srvRestT E γr T A` in `InvRest` (`srvRest E γr A := srvRestT E γr (appliedTable γr A) A`, so the off proofs are
   untouched) and `srvRestM on E γr A := if on then srvRestT E γr (appliedTableM true γr A) A else srvRest E γr A` in a
   module after `KVModelM`; `srvRestRp`/`imageLeasesAt` and the auth-on users take `srvRestM E.authOn` (Draft §4's
   "`srvRest` and `srvRestAt`'s callers use `appliedTableM E.authOn`", in a Lean shape that fits the import order).

Next, in order:
1. §4: `srvRestT`/`srvRestM` as above; `srvRestRp` (`ApplyRDefs.lean:64`) and `imageLeasesAt` (`ImageLeases.lean:51`) at
   the mode; the auth-on users switch (with the TRANSITIONAL row still in place they only rewrite: `E.lg = false`).
2. §5: drop `γr.kv.lg = false` from `srvKVInvsOn` (`KVApplyOn.lean:401`) and the TRANSITIONAL sites (`grep -rn
   TRANSITIONAL Proof`: `ApplyAllSnap:279`, `ApplyEntryOn:151`, `EtcdServer__applyEntryNormal:1293, 1513`,
   `MergedImageOn:88`, `SnapApplyPost:100` (`srvKVInvsM_lg`), `SnapRecvOn:537`), restate `specSnapM`'s `hnl` with
   `keysLeasesLive` (frozen rev 5 text, §5's table); the keys' invariants' preservation (`keysNonEmpty`,
   `keysLeasesLive`) in `kvInvOn`.
3. §6: the mode-`on` apply proofs (grant, revocation arms; the KV branch over `kvOutL` + `leaseExactL`, no `plainCover`).
4. The land-stop checks (handoff "Build"; tcb 870/4, gen-interface with `Alloc3On.txt`, bounds, modes, closed statements,
   merge lean, no TRANSITIONAL markers).

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
