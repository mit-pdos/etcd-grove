/-
`(clientv3.Cmp).WithRange` (`client/v3/compare.go`).

Users: leasing (`leasing/txn.go`: comparisons over a range), `client/v3/concurrency` (`election.go`: `Compare(CreateRevision(pfx), ...)` with `WithPrefix`).

Proof sketch: a clone (`Cmp.Clone.spec`), `Cmp.ensureCompare.spec`, the range end written.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Cmp__WithRange.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.
verify-round: premise `e ≠ []` (A1-provability F5): `WithRange("")` stores a non-`nil` empty end,
which a member reached over gRPC decodes as `nil` (the key alone) and the model reads as every key
from the key on (`Wire.endOf`, mvcc's in-process reading); the scope premise of `Api.lean`'s "Range
ends" (`nonissues/etcd-client-withrange-empty-end.md`). Every caller in scope passes a non-empty
end (leasing's `guardRanges` only for a non-empty `RangeBytes`).

Margin: none (the premise is a scope restriction, not the code's need: Go accepts `""`).
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

/-- `cmp.WithRange(...)`: a copy comparing over the range `[key, end)` (an empty `end`, a non-`nil` empty slice, reads as every key from the key on). -/
def Cmp.WithRange.spec : Prop :=
  ∀ (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare) (e : GoString) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpAt c m ∗ ⌜e ≠ []⌝ }}
    (App (Val (c @!! go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"WithRange")) (Val #e))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cmpAt c' (some { m.getD Compare.zero with rangeEnd := e }) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
