/-
`(*watchStream).Chan()`: the stream's channel.

**Users.** `serverWatchStream.sendLoop` (`v3rpc/watch.go:425, 516, 536`, 2b: the receive in its
`select`, the drain before a `Created`, the drain at its end). **Proof sketch.** Reads `ch`
(read-only). **Changes.** Unchanged. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import SpecPlan.Spec.context.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watchStream.Chan.spec : Prop :=
  ∀ (w : Loc) (γ : MvccName) (ι : WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι }}
    (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"Chan")) (Val #()))
  {{ RET #(wsChanOf ι); True }}

end spec

end Mvcc
end EtcdGrove
end Perennial
