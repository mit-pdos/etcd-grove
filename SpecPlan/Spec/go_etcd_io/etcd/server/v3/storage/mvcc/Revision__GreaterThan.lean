/-
`Revision.GreaterThan(b)` (`revision.go:44`): lexicographic on `(Main, Sub)`, signed. Internal
(`keyIndex.put`, the hasher). **Changes** from `specs-ref`'s file: over `Internal.lean`'s `Rev.gt`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `a.GreaterThan(b)`: `Rev.gt`. -/
def Revision.GreaterThan.spec : Prop :=
  ∀ (a b : Revision),
  {{ pkgInit }}
    (App (Val (a @!! Revision.ty @!! go!"GreaterThan")) (Val #b))
  {{ RET #(Rev.gt (revOf a) (revOf b)); True }}

end spec
end Mvcc
end EtcdGrove
end Perennial
