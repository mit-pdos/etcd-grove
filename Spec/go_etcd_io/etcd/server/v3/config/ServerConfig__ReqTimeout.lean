/-
`config.ServerConfig.ReqTimeout` (`config.go`: a duration computed from two fields). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

-- `InvServer`'s `ServerConfig` `TypeRepr` instances: without them the proof's field steps find
-- `TypeRepr` through the generated `IntoValTyped`, built from the axiomatized field types'
-- `sorry` instances (`TLSInfo`, `URLs`, `DiscoveryConfig`)
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

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

/-- `c.ReqTimeout()` (`5s + 2 * ElectionTicks * TickMs`, the fields read-only, as the server's
`Cfg` is): some duration (the proposal's timeout, which the model does not read). -/
abbrev config.ServerConfig.ReqTimeout.spec : Prop :=
  ∀ (c : Loc) (et tm : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"ElectionTicks" c ↦□ et ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"TickMs" c ↦□ tm }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"ReqTimeout"))
      (Val #()))
  {{ (d : time.Duration), RET #d; True }}

end spec

end EtcdGrove
end Perennial
