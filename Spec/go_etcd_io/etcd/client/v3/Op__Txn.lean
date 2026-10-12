/-
`clientv3.Op.Txn()` (`client/v3/op.go`, translated for `client/v3/leasing`); see `InvEtcdTxnOwn.lean` (`OpT`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.Txn()`: the `Op`'s comparisons, then- and else-operations (its three slice fields). -/
abbrev Op.Txn.spec : Prop :=
  ∀ (op : go_etcd_io.etcd.client.v3.Op),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (op @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"Txn")) (Val #()))
  {{ RET (PairV (PairV #op.cmps' #op.thenOps') #op.elseOps'); True }}

end spec

end EtcdGrove
end Perennial
