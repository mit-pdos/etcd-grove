/-
`notifier.wait` (`cache/*.go`), an internal helper.
Users: `demux.WaitForNextResync`.
Proof sketch: reads the channel under the read lock, then a `select` on it and `ctx.Done()`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: `nil` means a notification happened after the call read the channel; not stated (no caller uses it).
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

/-- `n.wait(ctx)`: `nil` (a notification came), or the context's error once done. -/
def notifier.wait.spec : Prop :=
  ∀ (n : Loc) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isNotifier n ∗ Context.ctxOk ctx ∗ threadTok }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.notifier.ty @!! go!"wait")) (Val #ctx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ⌜err = GoInterface.nil⌝ ∨ (Context.ctxDone ctx ∗ context.isCtxErr err) }}

end spec

end Cache
end EtcdGrove
end Perennial
