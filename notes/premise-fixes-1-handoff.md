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

## Status

See the commits on the branch; the stage stops before `etc/land.sh`.

## Pitfalls

- `NewServer.lean` is a large compile (cap 64G); don't edit files it imports while it builds.
- `notes/status-history.md` is append-only: check `wc -l` against lean's before committing it.
