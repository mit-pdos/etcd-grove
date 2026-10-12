/-
`firstOpLease(ops)` (`tracing.go`): the first put's lease (a trace attribute).
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `firstOpLease(ops)` on the operations of a request (`requestOpsIs`) returns some value. -/
abbrev firstOpLease.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      sl ↦*□ ps ∗ txn.requestOpsIs ps ops }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.firstOpLease)) (Val #sl))
  {{ (l : w64), RET #l; True }}

end spec

end EtcdGrove
end Perennial
