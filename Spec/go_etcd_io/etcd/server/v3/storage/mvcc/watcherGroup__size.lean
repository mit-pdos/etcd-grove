/-
`(*watcherGroup).size()` (internal): the number of watchers.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

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

def watcherGroup.size.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq dq' : DFrac) (G : List (Loc × MRange)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v dq' G }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"size")) (Val #()))
  {{ RET #(W64 G.length); wg ↦{dq} v ∗ wgOwn v dq' G }}

end spec

end Mvcc
end EtcdGrove
end Perennial
