/-
`config.ServerConfig.ElectionTimeout` (`config.go`: a duration computed from two fields).
Lean-first (no Rocq counterpart).
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

/-- `c.ElectionTimeout()` (`c.ElectionTicks` and `c.TickMs` read-only, as the server's `Cfg`
is) returns some duration. -/
abbrev config.ServerConfig.ElectionTimeout.spec : Prop :=
  ∀ (c : Loc) (et tm : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      cfgElectionTicksAddr c ↦□ et ∗ cfgTickMsAddr c ↦□ tm }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"ElectionTimeout")) (Val #()))
  {{ (d : w64), RET #d; True }}

end spec

end EtcdGrove
end Perennial
