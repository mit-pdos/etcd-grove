/-
`mkGteRange(rangeEnd)` (`delete.go`), internal: mirrors the code (`"\x00"`, "every key from the key
on", becomes the empty non-`nil` slice mvcc's index reads as unbounded). Old spec: same.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

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
/-- `mkGteRange(rangeEnd)`: `[0]` becomes `[]byte{}` (non-`nil`), anything else is returned. -/
def mkGteRange.spec : Prop :=
  ∀ (rend : GoSlice) (e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ rend ↦*□ e }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange)) (Val #rend))
  {{ (r : GoSlice), RET #r; r ↦*□ (if e = [W8 0] then [] else e) ∗
      ⌜if e = [W8 0] then r ≠ slice.nil else r = rend⌝ }}

end spec
end Txn
end EtcdGrove
end Perennial
