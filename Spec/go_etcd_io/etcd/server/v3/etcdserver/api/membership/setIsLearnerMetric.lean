/-
## `setIsLearnerMetric(m)` (`metrics.go`): names only

**Users.** `AddMember`, `Recover`. **Why it is true.** Reads the learner flag; sets a gauge.
**Changes**: from `specs-ref`. **Margin.** None.
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

/-- **Sets the learner gauge** from the member's flag. -/
def setIsLearnerMetric.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : Member),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ memberPts p dq m }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.setIsLearnerMetric)) (Val #p))
  {{ RET #(); memberPts p dq m }}

end spec

end Membership
end EtcdGrove
end Perennial
