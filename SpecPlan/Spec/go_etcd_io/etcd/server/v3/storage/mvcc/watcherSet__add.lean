/-
`watcherSet.add(wa)` (internal): `wa` added (`panic` if present: the premise).
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

def watcherSet.add.spec : Prop :=
  ∀ (m : GoMap) (S : List Loc) (wa : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsetOwn m (DFrac.own 1) S ∗ ⌜wa ∉ S⌝ }}
    (App (Val (m @!! watcherSet.ty @!! go!"add")) (Val #wa))
  {{ RET #(); wsetOwn m (DFrac.own 1) (S ++ [wa]) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
