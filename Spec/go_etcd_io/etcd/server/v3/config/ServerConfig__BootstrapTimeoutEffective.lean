/-
`(*config.ServerConfig).BootstrapTimeoutEffective()` (`config.go:345-350`); claim #34, stage 2,
2026-11-25: translated with its body). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.config
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.net.http.Boundary

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`c.BootstrapTimeoutEffective()`**: some duration (the configured one, or a second). -/
abbrev config.ServerConfig.BootstrapTimeoutEffective.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗ p ↦{dq} cfg }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"BootstrapTimeoutEffective")) (Val #()))
  {{ (d : w64), RET #d; p ↦{dq} cfg }}

end spec

end EtcdGrove
end Perennial
