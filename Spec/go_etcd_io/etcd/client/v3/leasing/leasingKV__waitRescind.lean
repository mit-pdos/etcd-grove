/-
`(*leasingKV).waitRescind` (`kv.go`): watches the lease key from `rev + 1` until a delete, then
returns `ctx.Err()` (`nil` also when the watch ends early: `issues/leasing-wait-rescind-no-delete.md`).
Proof sketch: `Context.WithCancel.spec` (W0), `Watcher.Watch` (1b), `ctx.Err()`
(`Context.Err.spec`). Changes: from `specs-ref`'s `leasingKV__waitRescind.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `waitRescind(ctx, key, rev)`: `nil`, or (`ctx` done) its error. -/
def leasingKV.waitRescind.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin ctx who }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"waitRescind")) (Val #ctx)) (Val #key)) (Val #rev))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ (Context.ctxDone ctx ∗ context.isCtxErr err) }}

end spec

end Leasing
end EtcdGrove
end Perennial
