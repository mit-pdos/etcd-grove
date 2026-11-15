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
     leased puts at the revocable mode. Design: `notes/auth-lease-s3a-draft.md`.
   - **S3b**: the request side (grant, revoke, leased put with auth on).
   - **S3c**: the couplings and `NewServer`; the `lease.bootCfg` hub change and the `NewLessor` docstring (hard stops).
   - The auth-on snapshot path carries the leases (F2 (a)); the latest track gains a lease-exact outcome (F1 (ii)).
2. S4 with the client's leased put (`WithLease`, `Put`/`Txn` with a lease) and linearizable client specs of
   `Lease.Grant`/`Revoke` (F3).

## Pitfalls

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
