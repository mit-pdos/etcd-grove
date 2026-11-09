/-
`(*EtcdServer).FeatureEnabled(f)` (`server.go:456-458`): `s.Cfg.ServerFeatureGate.Enabled(f)`.

**Users**: v3rpc's health server (`health.go:39`), `NewServer`'s feature checks.

**Proof sketch**: the read-only `s.Cfg` (`srvMember`'s realization: its feature gate, read-only after `NewServer`); the gate's `Enabled` (`features`' spec: a lookup under its own lock; a known feature, any answer).

**Changes**: verify round (A7-completeness F3): new here (the old tree's
`EtcdServer__FeatureEnabled.lean`).

**Margin**: the answer is any boolean.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`FeatureEnabled(f)`**: a boolean (any). -/
def EtcdServer.FeatureEnabled.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (f : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"FeatureEnabled")) (Val #f))
  {{ (b : Bool), RET #b; threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
