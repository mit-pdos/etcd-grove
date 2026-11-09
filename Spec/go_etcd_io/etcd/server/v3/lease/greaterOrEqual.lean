/-
`greaterOrEqual(first, second)` (`lessor.go:390`), an internal helper's spec (mirrors the code).
**Users**: `shouldPersistCheckpoints`. **Proof sketch**: `!version.LessThan(first, second)`
(`api/version`'s `LessThan.spec`, 3h's assumed spec, `Spec/go_etcd_io/etcd/api/v3/version/
LessThan.lean`: some boolean, no panic). **Changes** (from
`specs-ref`'s `greaterOrEqual.lean`): the result any boolean (no spec needs which). **Margin**: the
comparison's value.
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

/-- **Whether version `first` is at least `second`** (some boolean). -/
def greaterOrEqual.spec : Prop :=
  ∀ (first second : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.greaterOrEqual)) (Val #first)) (Val #second))
  {{ (b : Bool), RET #b; True }}

end spec
end Lease
end EtcdGrove
end Perennial
