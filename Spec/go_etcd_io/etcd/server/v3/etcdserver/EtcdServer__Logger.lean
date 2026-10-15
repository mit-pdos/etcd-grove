/-
`EtcdServer.Logger` (`server.go`: it reads `s.lg` under `s.lgMu`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

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

/-- `s.Logger()` returns the server's (non-nil) logger, read under `s.lgMu`'s read lock (the
caller's reader slot, `srvLgReader`, given back). -/
abbrev EtcdServer.Logger.spec : Prop :=
  ∀ (s l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗ srvLgReader s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Logger")) (Val #()))
  {{ RET #l; ⌜l ≠ null⌝ ∗ srvLgReader s }}

end spec

end EtcdGrove
end Perennial
