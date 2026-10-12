/-
`etcdserverpb.RequestOp.GetRequestRange()` (`api/etcdserverpb/rpc.pb.go`, translated for the
server's `txn.IsTxnReadonly`/`IsTxnSerializable`). Lean-first (no Rocq counterpart); see the txn
package's `Requests.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `op.GetRequestRange()` of a `*pb.RequestOp` denoting `op` (`txn.requestOpIs`): its range
request if it is a range, else `nil`. -/
abbrev RequestOp.GetRequestRange.spec : Prop :=
  ∀ (p : Loc) (op : TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ txn.requestOpIs p op }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.RequestOp.ty @!! go!"GetRequestRange"))
      (Val #()))
  {{ (r : Loc), RET #r;
      match op with
      | .get o => txn.rangeRequestIs r o
      | _ => ⌜r = null⌝ }}

end spec

end EtcdGrove
end Perennial
