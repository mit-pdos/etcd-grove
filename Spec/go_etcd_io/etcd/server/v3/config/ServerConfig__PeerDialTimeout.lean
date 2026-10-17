/-
`config.ServerConfig.PeerDialTimeout` (`config.go`: a duration computed from two fields): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `c.PeerDialTimeout()` (`1s + ElectionTicks * TickMs`, the fields read-only): some duration. -/
abbrev config.ServerConfig.PeerDialTimeout.spec : Prop :=
  ∀ (c : Loc) (et tm : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"ElectionTicks" c ↦□ et ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"TickMs" c ↦□ tm }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!!
      go!"PeerDialTimeout")) (Val #()))
  {{ (d : time.Duration), RET #d; True }}

end spec

end EtcdGrove
end Perennial
