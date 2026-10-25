/-
`EtcdServer.RequestID` (`server.go`: `return s.reqIDGen.Next()`, added in PR etcd#21401). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- `s.RequestID()`: calls `s.reqIDGen.Next()`, returning a fresh request ID (`idFresh`). -/
abbrev EtcdServer.RequestID.spec : Prop :=
  ∀ (s : Loc) (γi : IdNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvIdGen s γi ∗ idCred γi 1 }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"RequestID")) (Val #()))
  {{ (id : w64), RET #id; idFresh γi id }}

end spec

end EtcdGrove
end Perennial
