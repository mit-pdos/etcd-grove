/-
`(*lessor).shouldPersistCheckpoints()` (`lessor.go:385`), an internal helper's spec (mirrors the
code). **Users**: `Checkpoint`. **Proof sketch**: `le.cluster.Version()` (`clusterOk`, from
`isLessor`: `nil` or a readable version), `greaterOrEqual(*cv, version.V3_6)` (`greaterOrEqual.spec`;
`V3_6` is `api/v3/version`'s package variable, read from its initialization: 3h's), or
`le.checkpointPersist` (read-only). `clusterOk` is still provisional (2e has no `RaftCluster.Version`
spec). **Changes** (from `specs-ref`'s
`lessor__shouldPersistCheckpoints.lean`): over `isLessor`. **Margin**: the answer.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Whether checkpoints are persisted** (some boolean). -/
def lessor.shouldPersistCheckpoints.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"shouldPersistCheckpoints")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec
end Lease
end EtcdGrove
end Perennial
