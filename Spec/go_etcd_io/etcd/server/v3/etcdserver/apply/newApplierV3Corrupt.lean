/-
`newApplierV3Corrupt(a)` (`corrupt.go:27`): the corrupt applier over `a`.

**Users.** `uberApplier.restoreAlarms`.

**Proof sketch.** Allocation.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The corrupt applier over `a`.** -/
def newApplierV3Corrupt.spec : Prop :=
  ∀ (base : GoInterface) (ls : List Layer) (b aa : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ applierAt base ls b aa }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Corrupt)) (Val #base))
  {{ (c : Loc), RET #c; applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt.ty) #c) (Layer.corrupt :: ls) b aa }}

end spec

end Apply
end EtcdGrove
end Perennial
