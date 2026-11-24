/-
`(*config.ServerConfig).hasLocalMember()` (`config.go:241-246`); claim #34, stage 2,
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

/-- **`c.hasLocalMember()`**: an error, or the configuration's name an entry of the initial cluster's
map (read-only). -/
abbrev config.ServerConfig.hasLocalMember.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (m : GMap GoString GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗ p ↦{dq} cfg ∗ cfg.InitialPeerURLsMap' ↦$□ m }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"hasLocalMember")) (Val #()))
  {{ (err : GoInterface), RET #err; p ↦{dq} cfg ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil ∧ (m.lookup cfg.Name').isSome⌝) }}

end spec

end EtcdGrove
end Perennial
