/-
`(*leasingKV).Close` (`client/v3/leasing/kv.go`), the close function `NewKV` returns.

Users: the integration tests (`defer closeLKV()`); the proxy never calls it. Snippet:
`leasing/lifecycle.go` (`ReqNewKVClose`).

Proof sketch: `lkv.cancel()` (Perennial's cancel function, in `isLeasingKV`); `lkv.wg.Wait()` with
the whole open token, which the wait group's invariant takes: no `get` can `Add` any more (its
share is in the token), so the counter only falls (the monitors see `lkv.ctx` done and return,
`monitorSession`, `monitorLease`, `clearOldRevokes`), and `Wait` returns.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Close.lean`: the open
token renamed (`lkvOpen`, was `leasingOpen`); `isLeasingCancel` folded into `isLeasingKV`.

Margin: the session is not closed (its lease stays until it expires); nothing is given back.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Api

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

/-- **`lkv.Close()`**: with the whole open token, it returns. -/
def leasingKV.Close.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ lkvOpen γL 1 }}
    (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
