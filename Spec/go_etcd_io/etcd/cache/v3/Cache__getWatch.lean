/-
`Cache.getWatch()` (`cache/cache.go`): one round of the watch loop, a `get` then a `watch`.
Lean-first (no Rocq counterpart); see `InvCache.lean` and `InvEtcd.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.getWatch()`, by the demux's writer (`cacheWriter`, any state, with the revision bound) in a
goroutine of the cache's wait group: the client's prefix get, restored into the store (`get`),
then `watch` from the revision after the get's. It returns a non-nil error (the get's, or the
watch's), the wait-group token and the demux's writer, in some state. -/
abbrev Cache.getWatch.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (c0 : DemuxCore),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ cacheWriter cf γd cap c0 ∗ cacheWgRunning cf }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"getWatch")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ cacheWgRunning cf ∗
      ∃ c1 : DemuxCore, cacheWriter cf γd cap c1 }}

end spec

end EtcdGrove
end Perennial
