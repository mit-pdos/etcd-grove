/-
## `MembersByID.Less(i, j)` (`member.go:122`): translated

**Users.** `sort.Sort` in `Members()`. **Proof sketch.** Two pointer reads, two id reads.
**Changes**: from `specs-ref`. **Margin.** Exact.
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

/-- **Whether member `i`'s id is below member `j`'s.** -/
def MembersByID.Less.spec : Prop :=
  ∀ (sl : GoSlice) (dq dq' : DFrac) (ps : List Loc) (ms : List Member) (i j : w64) (mi mj : Member),
  ms[sint.nat i]? = some mi → ms[sint.nat j]? = some mj → ps.length = ms.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*{dq} ps ∗ ([∗list] pm ∈ ps.zip ms, memberPts pm.1 dq' pm.2) }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (mi.id < mj.id)); sl ↦*{dq} ps ∗
      ([∗list] pm ∈ ps.zip ms, memberPts pm.1 dq' pm.2) }}

end spec

end Membership
end EtcdGrove
end Perennial
