/-
`(*config.ServerConfig).ShouldDiscover()` (`config.go:311-313`) (claim #34, stage 2, 2026-11-25: translated with its body). Lean-first. The
configuration's fields are read through `p`, read-only (`↦□`), as the other `ServerConfig` specs.
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

/-- **`c.ShouldDiscover()`**: whether the discovery configuration has endpoints. -/
abbrev config.ServerConfig.ShouldDiscover.spec : Prop :=
  ∀ (p : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DiscoveryCfg" p ↦□ cfg.DiscoveryCfg' }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"ShouldDiscover")) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = true → cfg.DiscoveryCfg'.ConfigSpec'.Endpoints'.len ≠ W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
