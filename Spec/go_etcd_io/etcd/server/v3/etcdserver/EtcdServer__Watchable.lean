/-
`s.Watchable()` (`v3_server.go`: `return s.KV()`): the server's KV as a `mvcc.WatchableKV`.
Lean-first (no Rocq counterpart); the watch slice's unit W-S (2026-10-14).
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

/-- `s.Watchable()` returns `s.kv` (read-only). -/
abbrev EtcdServer.Watchable.spec : Prop :=
  ∀ (s : Loc) (kv : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvKVAddr s ↦□ kv }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Watchable")) (Val #()))
  {{ RET #kv; True }}

end spec

end EtcdGrove
end Perennial
