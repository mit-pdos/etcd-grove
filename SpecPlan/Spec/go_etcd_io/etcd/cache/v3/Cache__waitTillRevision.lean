/-
`Cache.waitTillRevision` (`cache/*.go`), an internal helper.
Users: `Cache.Get`.
Proof sketch: `store.LatestRev.spec`; `progressRequestor.add/remove` (deferred); a goroutine broadcasting `revCond` at the timeout or the context's end (not in the wait group: it ends by itself); under the store's read lock a loop on `latest.rev` with `revCond.Wait` (Perennial's `sync.Cond` over the read locker), the timeout (`time.Since`) and `ctx.Err()`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: the broadcasting goroutine outlives the call by up to `WaitTimeout` (a goroutine per waiting `Get`): no resource of the caller's is tied to it.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.waitTillRevision(ctx, rev)`: `nil` once the cache reached `rev`, else an error (`ErrCacheTimeout`, the context's). -/
def Cache.waitTillRevision.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (ctx : GoInterface) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ Context.ctxOk ctx ∗ threadTok }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"waitTillRevision")) (Val #ctx)) (Val #rev))
  {{ (err : GoInterface), RET #err; threadTok ∗
      (⌜err = GoInterface.nil⌝ ∗ cacheRevLb c (sint.Z rev).toNat) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
