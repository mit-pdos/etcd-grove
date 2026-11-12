/-
## `MembersByID.Swap(i, j)` (`member.go:123`): translated

**Users.** `sort.Sort` in `Members()`. **Proof sketch.** Two slice writes. **Changes**: from
`specs-ref`. **Margin.** Exact.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- **Swaps elements `i` and `j`.** -/
def MembersByID.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (i j : w64) (pi pj : Loc),
  ps[sint.nat i]? = some pi → ps[sint.nat j]? = some pj →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦* ps }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* ((ps.set (sint.nat i) pj).set (sint.nat j) pi) }}

end spec

end Membership
end EtcdGrove
end Perennial
