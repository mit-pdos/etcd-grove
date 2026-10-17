/-
`EtcdServer.RequestLogger` (`server.go`, etcd#21764: it reads `s.requestLogger`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequestLog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.RequestLogger()` returns `s.requestLogger` (read-only; nil when request logging is off). -/
abbrev EtcdServer.RequestLogger.spec : Prop :=
  ∀ (s rl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvReqLgAddr s ↦□ rl }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"RequestLogger")) (Val #()))
  {{ RET #rl; True }}

end spec

end EtcdGrove
end Perennial
