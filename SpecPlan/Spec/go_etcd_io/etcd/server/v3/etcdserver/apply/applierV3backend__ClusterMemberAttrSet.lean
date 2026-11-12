/-
`(*applierV3backend).ClusterMemberAttrSet(r, shouldApplyV3)` (`backend.go:287-296`): the member's name and client URLs set (`RaftCluster.UpdateAttributes`).

**Users.** `uberApplier.dispatch` (through the outer layers' promoted methods), in both modes.

**Proof sketch.** 2e's `RaftCluster.UpdateAttributes.spec` with the caller's update (`memberUpd`) and the backend's member buckets (`beView`, inside `stAt`: moved with `shouldApplyV3`).

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **A member's attributes published**: the view by the caller's update; the model's members with `shouldApplyV3`. -/
def applierV3backend.ClusterMemberAttrSet.spec : Prop :=
  ∀ (p rq : Loc) (v3 : Bool) (id : Nat) (name : GoString) (urls : List GoString) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF)
    (σ : State) (Qm : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ beAt p mc γ γc R ∗ stAt p σ ∗ reqMsgAt rq (.memberAttrSet id name urls) ∗
      memberUpd γc (.memberAttrSet id name urls) Qm ∗ threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"ClusterMemberAttrSet")) (Val #rq)) (Val #v3))
  {{ RET #(); Qm ∗ threadTok ∗ stAt p (if v3 then publish σ id name urls else σ) }}

end spec

end Apply
end EtcdGrove
end Perennial
