/-
## `(*ServerConfig).PeerDialTimeout()` (`config.go:316-329`)

**Users.** `bootstrap`'s round tripper, the transport. **Proof sketch.** Two field reads, Go's wrapping arithmetic. **Changes**: from
`specs-ref`'s `ServerConfig__PeerDialTimeout.lean` (post `True`): the value is stated, as Go computes it.
**Margin.** Exact.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Config

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

/-- **`PeerDialTimeout()`**: the configuration's value, Go's wrapping arithmetic. -/
def ServerConfig.PeerDialTimeout.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig),
  {{ (typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"ElectionTicks" c) cfg.ElectionTicks' DFrac.discard ∗ typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"TickMs" c) cfg.TickMs' DFrac.discard : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"PeerDialTimeout")) (Val #()))
  {{ RET #(Config.peerDialTimeoutOf cfg); True }}

end spec

end Config
end EtcdGrove
end Perennial
