/-
`(*leasingKV).monitorLease` (`kv.go`): the goroutine a `get` starts after an acquisition; watches
the lease key and rescinds on `"REVOKE"`. Proof sketch: `kv.Get` of the lease key (a read:
`protoUpd`), `Watcher.Watch` (1b's `watcherAt`; its events read-only), `leaseID` (a reader slot of
the thread's own token), `rescind`. Changes: from `specs-ref`'s `leasingKV__monitorLease.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `monitorLease(ctx, key, rev)`: runs until it rescinds or the KV's context is done. -/
def leasingKV.monitorLease.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ threadTok }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"monitorLease")) (Val #ctx)) (Val #key)) (Val #rev))
  {{ RET #(); threadTok }}

end spec

end Leasing
end EtcdGrove
end Perennial
