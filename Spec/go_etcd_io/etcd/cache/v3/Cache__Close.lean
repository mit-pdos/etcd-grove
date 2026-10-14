/-
`Cache.Close()` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.Close()`: cancels the internal context (`c.stop()`) and waits for the cache's goroutines
(`c.waitGroup.Wait()`: the resync loop, the watch loop, the progress requestor and the `Watch`
goroutines). It needs the whole "open" token (`cacheOpen cf 1`: no `Watch` runs meanwhile, as
Perennial's `WaitGroup` forbids an `Add` from zero while `Wait` waits) and gives it back. The
goroutines hand nothing back through the wait group, so the postcondition says nothing more. -/
abbrev Cache.Close.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ cacheOpen cf 1 }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"Close")) (Val #()))
  {{ RET #(); cacheOpen cf 1 }}

end spec

end EtcdGrove
end Perennial
