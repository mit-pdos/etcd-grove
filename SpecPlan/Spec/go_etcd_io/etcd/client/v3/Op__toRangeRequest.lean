/-
`(clientv3.Op).toRangeRequest` (`client/v3/op.go`).

Users: `kv.Do` (a range).

Proof sketch: `opAt_unfold`; a fresh `RangeRequest` with the `Op`'s fields (its key and range end the `Op`'s read-only slices; the sort fields converted to `int32`); `rangeReqOwn_unfold`. Panics unless `t = tRange` (premise).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Op__toRangeRequest.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

verify-round (re-review NF1): premise `o.emptyEnd = false` (no non-`nil` empty range end at any
depth): the request message's unfold law now carries `es = slice.nil ∨ ebs ≠ []` (`Wire.lean`), which
the built message would not meet otherwise; every caller has it (the KV triples' scope premise).

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

/-- `op.toRangeRequest()` of a range: its request, owned. -/
def Op.toRangeRequest.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opAt op o ∗ ⌜o.t = tRange ∧ o.emptyEnd = false⌝ }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRangeRequest")) (Val #()))
  {{ (p : Loc), RET #p; opp ↦{dq} op ∗ rangeReqOwn p (DFrac.own 1) o.rangeReq }}

end spec

end ClientV3
end EtcdGrove
end Perennial
