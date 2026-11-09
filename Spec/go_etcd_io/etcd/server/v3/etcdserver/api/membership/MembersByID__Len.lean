/-
## `MembersByID.Len()` (`member.go:121`): translated

**Users.** `sort.Sort` in `Members()`. **Proof sketch.** `len`. **Changes**: from `specs-ref`.
**Margin.** Exact.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

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

/-- **The number of members.** -/
def MembersByID.Len.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ps : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ sl ↦*{dq} ps }}
    (App (Val (sl @!! go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 ps.length); sl ↦*{dq} ps }}

end spec

end Membership
end EtcdGrove
end Perennial
