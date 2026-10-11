/-
`Cache.watch(rev)` (`cache/cache.go`): the watch loop proper, between two `get`s. Lean-first (no
Rocq counterpart); see `InvCache.lean` and `InvEtcd.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.watch(rev)`, by the demux's writer (`cacheWriter`, any state, with the revision bound) in a
goroutine of the cache's wait group (`cacheWgRunning`), when the store's newest snapshot is at
least `R` with `0 < rev ≤ R + 1`: it initializes the demux at `rev` (`Init`), then loops: it
registers a fresh store watcher from `rev` (`newWatcher`, `Register`), adds a goroutine to the wait
group (`Add(1)`, which may not overflow the counter: Perennial's model assumption) that runs
`applyStorage` on it and then hands its error over on `applyErr` or closes it, runs `watchEvents`,
and unregisters the store watcher (which stops it); it returns `watchEvents`'s first non-nil
error.

It does not wait for the goroutine: a stopped watcher's buffered responses may still be applied
while the next iteration (or, after `watch` returns, the next `get`'s `Restore`) runs. The store
is shared by its writers (`isStoreWriter`), and the goroutine needs only the store's newest
snapshot at least `rev - 1`, which stays true. Each goroutine keeps its own watcher's consumer; an
`applyErr` nobody reads is fine (buffered, capacity one).

It returns a non-nil error, the wait-group token, and the demux's writer, in some state. -/
abbrev Cache.watch.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (rev R : w64) (c0 : DemuxCore),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ cacheWriter cf γd cap c0 ∗ cacheWgLoopRunning cf ∗
      storeSnapLb cf.γs R ∗ ⌜0 < sint.Z rev ∧ sint.Z rev ≤ sint.Z R + 1⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"watch")) (Val #rev))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ cacheWgLoopRunning cf ∗
      ∃ c1 : DemuxCore, cacheWriter cf γd cap c1 }}

end spec

end EtcdGrove
end Perennial
