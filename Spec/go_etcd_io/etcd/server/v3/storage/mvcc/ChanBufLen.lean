/-
`ChanBufLen` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `Base.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `ChanBufLen()`: the package variable `chanBufLen`, `128` (only tests change it). -/
abbrev mvcc.ChanBufLen.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ChanBufLen)) (Val #()))
  {{ RET #(W64 128); True }}

end spec

end EtcdGrove
end Perennial
