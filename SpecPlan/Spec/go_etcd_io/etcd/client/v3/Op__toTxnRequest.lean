/-
`(clientv3.Op).toTxnRequest` (`client/v3/op.go`).

Users: `kv.Do` (a transaction), `Op.toRequestOp` (a nested one).

Proof sketch: two fresh slices of `toRequestOp.spec`'s results, the comparisons cloned (`Cmp.Clone.spec`, `Cmp.GetCompare.spec`); `txnReqOwn_unfold`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Op__toTxnRequest.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `op.toTxnRequest()`: the `TxnRequest` of its comparisons and branches, owned. -/
def Op.toTxnRequest.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (dq : DFrac) (s f : List RequestOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opAt op o ∗
      ⌜OpM.toReqOps o.thenOps = some s ∧ OpM.toReqOps o.elseOps = some f ∧ o.emptyEnd = false⌝ }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"toTxnRequest")) (Val #()))
  {{ (p : Loc), RET #p; opp ↦{dq} op ∗
      txnReqOwn p (DFrac.own 1)
        { compare := o.cmps.map (fun c => c.getD Compare.zero), success := s, failure := f } }}

end spec

end ClientV3
end EtcdGrove
end Perennial
