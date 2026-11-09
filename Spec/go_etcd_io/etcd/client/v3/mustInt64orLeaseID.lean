/-
`clientv3.mustInt64orLeaseID` (`client/v3/compare.go`).

Users: `Compare` (a `LeaseValue` comparison).

Proof sketch: a type assertion to `LeaseID`, else `mustInt64.spec`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/mustInt64orLeaseID.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `mustInt64orLeaseID(v)` of a `LeaseID`, an `int64` or an `int`: its value. -/
def mustInt64orLeaseID.spec : Prop :=
  ∀ (a : CmpArg) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ⌜a = .i64 n ∨ a = .int n ∨ a = .leaseID n⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.mustInt64orLeaseID)) (Val #(a.toIface)))
  {{ RET #n; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
