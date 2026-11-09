/-
`watcherSetByKey.add(wa)` (internal): `wa` added to its key's set (a new set if none; `panic` if
present: the premise).
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

def watcherSetByKey.add.spec : Prop :=
  ∀ (m : GoMap) (K : Key → List Loc) (wa : Loc) (ι : WsNames) (id : w64) (W : WatcherM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wskOwn m K ∗ watcherAt wa ι id W ∗ ⌜wa ∉ K W.range.key⌝ }}
    (App (Val (m @!! watcherSetByKey.ty @!! go!"add")) (Val #wa))
  {{ RET #(); wskOwn m (fun k => if k = W.range.key then K k ++ [wa] else K k) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
