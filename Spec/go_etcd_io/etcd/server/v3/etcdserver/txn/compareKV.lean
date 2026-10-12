/-
`compareKV` (`txn.go`). Lean-first; see `TxnRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `compareKV(c, ckv)`: the client model's `cmpKv` of the comparison `c` denotes against the
key-value `ckv` holds (read-only). -/
abbrev txn.compareKV.spec : Prop :=
  ∀ (c ckv : Loc) (cm : CmpModel) (v : EtcdKv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.compareIs c cm ∗ txn.kvIs ckv v }}
    (App (App (Val (@! txn.compareKV)) (Val #c)) (Val #ckv))
  {{ RET #(cmpKv cm v); True }}

end spec

end EtcdGrove
end Perennial
