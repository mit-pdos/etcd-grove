# WAL W4c: handoff

Branch `wal-w4c`, worktree `/shared/etcd-grove-walw3`, cut from lean `219ddbbb83` (W4b landed;
`wal-w4b` deleted). Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4c/`.

Goal (the user, 2026-11-11): the first rung of the crash ladder. Prove that the WAL robustness tester
(`examples/etcd/wal`) never panics under kill, power loss and kill-then-power-loss crashes, over
the crash-aware WAL spec (W4a, W4a.1, W4a.2, W4b). The closed theorems are `etcd_wal_adequate` and
`etcd_wal_safe`.

## State (2026-11-12, first agent)

- Plan written: `/shared/tmp/wal-spec/w4c/plan.md`. **Hard stop: waiting for etcd-grove-81** on its
  §7 decisions:
  - Q1: durable crash interpretation with fresh ghost names per generation, plus keep views (shared
    with rung 3);
  - Q2: purgeRound names-only with one axiom (PR-a);
  - Q3: the tester's check tracks the model's purge bounds;
  - Q4: `walCreateOk` as a premise;
  - Q5: tester changes T-1..T-9.
- No Lean edited or built. No scratch probe was needed.

## Next, in order (after approval; plan §8)

0. Step 0 (Go; no Lean), then CP1:
   - create `examples/etcd/wal` from `/shared/tmp/wal-spec/w3b/tester/etcd/wal` with T-1..T-9, and
     move the driver beside it;
   - add the goose project `etcd-wal` (as `restart3`) and run the translation;
   - run `etc/gen-init.py` over the closure (risk R1: `fileutil`);
   - rerun the W3b matrix with the new check: 0 violations required.
1. PR-a's axiom and its Freeze (hard stop).
2. Q1, `Defs`/`RefLemmas`/`Crash`, then CP2.
3. Per-function proofs, then CP3.
4. `Results`/`Link`/Init/tcb collection, then the hard stop on the closed theorem.

## Pitfalls

- **The crash obligation runs at `⊤` and cannot refute `crashed`.** So the old generation's invariant
  must be closed with its contents kept (crashlog's `cfInv_crash_keep`). This is why the durable
  extension's identity crash interpretation does not work for an invariant that also holds the WAL
  (plan §0.4).
- The landed `"WalPurge"` takes `k` by value: no `TrustedCode` model can perform it (plan §0.5).
- Since W4a revision 3, `Open` raises `unl` (persisting across crashes, clamped), so the tester's old
  `released`-based check is stronger than the spec (plan §0.3).
- The tester's oracle stores must precede the calls they cover: the `unl` bound before
  `ReleaseLockTo`, `pur` before `purgeRound`, `opens` before each `Open`.
- GOWORK=off only for our own Go test runs; never in the shell of `etc/goose.py`/`gates.sh`/`land.sh`.
- `notes/status-history.md` is append-only.

## Build command

```
export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build <module>
# full: flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
