/-
`compareKV(c, ckv)` (`txn.go`), internal: mirrors the code (W0's `Compare.holdsOf`; the numbers
compared as `int64`: `kvFits`). Old spec: same.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

open Classical in
/-- `compareKV(c, kv)`: W0's `Compare.holdsOf`. -/
def compareKV.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (cm : EtcdModel.Compare) (p : Loc) (dq' : DFrac) (kv : KV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ compareOwn c dq cm ∗ keyValueOwn p dq' (KeyValueM.ofKV kv) ∗ ⌜kvFits kv⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.compareKV)) (Val #c)) (Val #p))
  {{ RET #(decide (cm.holdsOf kv)); compareOwn c dq cm ∗ keyValueOwn p dq' (KeyValueM.ofKV kv) }}

end spec
end Txn
end EtcdGrove
end Perennial
