/-
`clientv3.NewMaintenance` (`client/v3/maintenance.go`).

Users: `newClient`.

Proof sketch: the retry wrapper over the client's connection (`Retry*Client`'s spec, from
`clientConnOk`), the client's `callOpts` (`callOptsOk _ false`), the logger, the dial closure (`c.Dial`: `clientCore`); persisted.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/NewMaintenance.lean`: over `clientCore`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewMaintenance(c)`: a `*maintenance` of the client's cluster and principal. -/
def NewMaintenance.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewMaintenance)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ a : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty) #a⌝ ∗ maintHandle a c γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
