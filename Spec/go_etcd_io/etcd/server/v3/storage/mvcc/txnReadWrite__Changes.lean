/-
`txnReadWrite__Changes` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `trw.Changes()` returns `nil` (any `trw`: the method reads nothing). -/
abbrev mvcc.txnReadWrite.Changes.spec : Prop :=
  ∀ (trw : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Changes")) (Val #()))
  {{ RET #(slice.nil : GoSlice); True }}

end spec

end EtcdGrove
end Perennial
