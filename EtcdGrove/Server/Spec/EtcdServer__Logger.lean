/-
`EtcdServer.Logger`: the trust boundary (names-only: it reads `s.lg` under `s.lgMu`). Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Server.InvApplier

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Logger()` returns the server's (non-nil) logger. -/
abbrev EtcdServer.Logger.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Logger")) (Val #()))
  {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
