# Premise fixes 1: handoff

Stage of etcd-grove-81's session agent (branch `premise-fixes-1`, worktree `/shared/etcd-grove-pfix`,
off lean `037bf21c75`). Three confirmed soundness bugs that made closed theorems vacuous, from the
read-only premise attack (evidence `/shared/tmp/premise-attack/`).

## Build command

```
export TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build <modules>
# full: flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake ... build
```

## Fixes, in order

1. **`Float64ToInt64Semantics` deleted** (it contradicted Perennial's
   `Float64Semantics.convert_float64_to_integer`; False in `/shared/tmp/premise-attack/dialfloat/FloatFalse.lean`).
   Its three users re-proved over Perennial's rule (`wp_ArbitraryInt` after the conversion):
   `NewServer` (the lessor's minimum TTL), `Reflector.watch` (the watch timeout),
   `TypedItemExponentialFailureRateLimiter.When` (the backoff). The binder removed from every result
   (`etc/gen-link.py`'s `SEM_PREMISES`; the Link files regenerate). Sweep of the other semantic
   hypothesis classes: no other contradiction (table in the stage report).
2. **`bootstrapContract`'s feature gate**: precondition `cfg.ServerFeatureGate' = nil ∨
   isFeatureGate ...` (as `storage.openPre`), discharged by `NewServer`; the same in
   `bootstrapRestartContract`. Go test `examples/premisefix/bootfg`.
3. **`bootMarshal`** restated over the conf change raft's `Bootstrap` builds (Type and NodeId set,
   Id unset, no unknown fields, contexts non-empty); **`pbMsg`** constrains the unknown fields to
   `[]` or what `proto.Unmarshal` leaves (`pbUnmarshalLeft`, opaque), which makes the Marshal
   round-trip axioms true. Go test `examples/premisefix/confchange`.
4. `ckptEffectsOk`'s docstring citation.
5. **`csPts` fixes a conf state's unknown fields to `[]`** (etcd-grove-81's review, 2026-11-10):
   false of a decoded `MsgSnap` (`proto.UnmarshalPb` at `pbMessage`, reached by every etcd closed
   theorem through rafthttp's decoders). Go test `examples/premisefix/confstate`. STOPPED before
   Lean: raft's `appliedSnap`/`newRaft` no-panic (`assertConfStatesEquivalent` → `Equivalent` →
   `proto.Equal`) needs the received conf state's unknown fields empty, which nothing in the model
   gives; options reported to etcd-grove-81 (recommended: a raft-fork change so `Equivalent`
   ignores unknown fields). Do not edit rafthttp's decoders (the raft-entsize agent owns them).

## Status (2026-11-10)

Done and committed: fix 1 (`c87acade60`), fix 2 (`0427e0b867`), fix 4 (`01e666e510`), fix 3
(`00e0cbcf74`); each built targeted (fix 1: all 431 importers; fixes 2/3: the changed proofs).
Then: interface regenerated (raft's), the full build and `etc/gates.sh` passed (2026-11-10: trust
base 809 axioms / 4 sorries unchanged, 53 collections match, premisefix Go tests ok). Fixes 1-4 approved by etcd-grove-81; the
protobuf docstrings fixed (form only). Fix 5 goes to `premise-fixes-2` (option 1, the raft fork's `Equivalent`, approved by the user via
etcd-grove-81). Lean merged (`de9c19e020`, stage A's `ufWire` supersedes `pbUnknownOk` in the main
tree); full build, interfaces and tcb check green; landing with `etc/land.sh`.
Open questions: `questions.md`.

## Pitfalls

- `NewServer.lean` is a large compile (cap 64G); don't edit files it imports while it builds.
- `notes/status-history.md` is append-only: check `wc -l` against lean's before committing it.
