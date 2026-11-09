/-
`(clientv3.Cmp).WithRange` (`client/v3/compare.go`).

Users: leasing (`leasing/txn.go`: comparisons over a range), `client/v3/concurrency` (`election.go`: `Compare(CreateRevision(pfx), ...)` with `WithPrefix`).

Proof sketch: a clone (`Cmp.Clone.spec`), `Cmp.ensureCompare.spec`, the range end written.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Cmp__WithRange.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `cmp.WithRange(...)`: a copy comparing over the range `[key, end)`. -/
def Cmp.WithRange.spec : Prop :=
  ∀ (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare) (e : GoString) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpAt c m }}
    (App (Val (c @!! go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"WithRange")) (Val #e))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cmpAt c' (some { m.getD Compare.zero with rangeEnd := e }) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
