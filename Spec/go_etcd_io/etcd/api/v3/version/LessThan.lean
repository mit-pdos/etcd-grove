/-
`version.LessThan(a, b)` (`api/version/version.go`): compares two `semver.Version`s by major and
minor.

Users: the lessor's `greaterOrEqual` (`lease/lessor.go:391`: whether the cluster supports
checkpointing, 3c).

**Assumed** (a translation gap): names only, as `Cluster`. True of the code: it compares two
integers of each value, no panic.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/version/LessThan.lean`: unchanged (some
boolean).
Margin: the answer is not specified (the lessor's spec does not depend on it).
-/
module

public import GeneratedProof.go_etcd_io.etcd.api.v3.version
public import Spec.PkgInit.go_etcd_io.etcd.api.v3.version

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Version

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

/-- `LessThan(a, b)`: some boolean. -/
def LessThan.spec : Prop :=
  ∀ (a b : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version }}
    (App (App (Val (@! go_etcd_io.etcd.api.v3.version.LessThan)) (Val a)) (Val b))
  {{ (r : Bool), RET #r; True }}

end spec

end Version
end EtcdGrove
end Perennial
