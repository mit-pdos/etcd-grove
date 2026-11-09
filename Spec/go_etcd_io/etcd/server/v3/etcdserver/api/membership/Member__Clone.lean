/-
## `(*Member).Clone()` (`member.go:90-112`): translated

**Users.** `Members()`. **Proof sketch.** A new struct, the URL slices copied. **Changes**: from
`specs-ref`. **Margin.** Exact.
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

/-- **A fresh copy of the member.** -/
def Member.Clone.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : Member),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ memberPts p dq m }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member.ty @!! go!"Clone")) (Val #()))
  {{ (p' : Loc), RET #p'; memberPts p dq m ∗ memberPts p' (DFrac.own 1) m }}

end spec

end Membership
end EtcdGrove
end Perennial
