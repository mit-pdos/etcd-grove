/-
`(*watchableStore).progressAll(watchers)` (internal; `watchStream.RequestProgressAll`'s callee,
under `ws.mu`): `progressIfSync` with the id `-1`.

**Proof sketch.** `progressIfSync` (its spec).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watchableStore.progressAll.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (ι : WsNames) (m : GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsMapAt m ι ∗ mvccReaders γ 1 }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"progressAll")) (Val #m))
  {{ (b : Bool), RET #b; wsMapAt m ι ∗ mvccReaders γ 1 }}

end spec

end Mvcc
end EtcdGrove
end Perennial
