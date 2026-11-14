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

## Next, in order

1. Land S1 when the coordinator says lean is free (merge lean first; `etc/land.sh`).
2. S2: finish the review rounds, then the Freeze package (hard stop), then the Lean Draft and Prove.
3. S3, S4 as the Scope.

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
