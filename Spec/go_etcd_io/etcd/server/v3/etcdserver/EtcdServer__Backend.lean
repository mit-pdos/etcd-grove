/-
`s.Backend()` (`server.go`): `s.be` under `s.bemu`'s read lock. Lean-first (no Rocq counterpart);
the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Backend()`, with a reader slot of `s.bemu` (given back): some backend. -/
abbrev EtcdServer.Backend.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvBemuReader s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Backend")) (Val #()))
  {{ (b : GoInterface), RET #b; srvBemuReader s }}

end spec

end EtcdGrove
end Perennial
