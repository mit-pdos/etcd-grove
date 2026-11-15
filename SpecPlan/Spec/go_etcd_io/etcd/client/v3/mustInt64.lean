/-
`clientv3.mustInt64` (`client/v3/compare.go`).

Users: `Compare`.

Proof sketch: two type assertions; `panic` otherwise (premise).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/mustInt64.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `mustInt64(v)` of an `int64` or an `int`: its value. -/
def mustInt64.spec : Prop :=
  ∀ (n : w64) (isInt : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.mustInt64)) (Val #(if isInt then (CmpArg.int n).toIface else (CmpArg.i64 n).toIface)))
  {{ RET #n; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
