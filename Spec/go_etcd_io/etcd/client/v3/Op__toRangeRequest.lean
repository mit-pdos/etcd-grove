/-
`clientv3.Op.toRangeRequest()` (`client/v3/op.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.toRangeRequest()` of a range `Op` without a sort option: a new `*pb.RangeRequest` (owned)
with the `Op`'s key and range end (read-only, shared with the `Op`) and fields, which the server
reads as `rangeWireOf o`. -/
abbrev Op.toRangeRequest.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opFullAt opv o ∗
      ⌜o.t = W64 1 ∧ o.base.sortSet = false⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRangeRequest")) (Val #()))
  {{ (r : Loc), RET #r; ∃ req : etcdserverpb.RangeRequest, r ↦ req ∗
      req.Key' ↦*□ o.key ∗ req.RangeEnd' ↦*□ o.base.rangeEnd ∗
      ⌜rangeReqOp req o.key o.base.rangeEnd = rangeWireOf o⌝ }}

end spec

end EtcdGrove
end Perennial
