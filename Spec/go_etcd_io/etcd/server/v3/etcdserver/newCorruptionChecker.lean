/-
## `newCorruptionChecker(lg, s, storage)` (`corrupt.go:63-73`)

**Users.** `NewServer` (`server.go:367`).

**Proof sketch.** A struct literal (`lg`, `hasherAdapter{s, storage}`), read-only for good.

**Changes**: from `specs-ref`'s `newCorruptionChecker.lean`: its handle named.

**Margin.** The checker's checks (`InitialCheck`, `PeriodicCheck`, `CompactHashCheck`) are not
specified: their only effect on the model is a `CORRUPT` alarm (`EnvStep.alarm`, any time), which
needs no guarantee; they are called by the monitors over `isServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_uber_org.zap.Api

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

/-- **Builds the corruption checker** of `s` over the hash storage. -/
def newCorruptionChecker.spec : Prop :=
  ∀ (lg s : Loc) (γ : Cluster) (id : Nat) (hs : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Zap.isLogger lg ∗ srvMember s γ id }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.newCorruptionChecker)) (Val #lg)) (Val #s)) (Val #hs))
  {{ (cc : Loc), RET #cc; isCorruptionChecker cc s hs }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
