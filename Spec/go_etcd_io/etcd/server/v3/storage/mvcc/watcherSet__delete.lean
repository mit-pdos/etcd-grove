/-
`watcherSet.delete(wa)` (internal): `wa` removed (`panic` if missing: the premise).
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

def watcherSet.delete.spec : Prop :=
  ∀ (m : GoMap) (S : List Loc) (wa : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsetOwn m (DFrac.own 1) S ∗ ⌜wa ∈ S⌝ }}
    (App (Val (m @!! watcherSet.ty @!! go!"delete")) (Val #wa))
  {{ RET #(); wsetOwn m (DFrac.own 1) (S.erase wa) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
