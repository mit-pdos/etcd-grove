/-
`(*authApplierV3).RoleGet(r)` (`auth.go:233-242`): the administrator, or a user with the role; then the base's.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 3d's `IsAdminPermitted`, `HasRole` (at the writer's `authCur`, with `authSt`'s
`Auth.authBeCur γa abe` and `hooksOk`'s `Auth.authBeHook abe R Q`, given back as `Q`, which
`□ (Q ={⊤}=∗ R)` turns into `R`; re-review A9 N1); the base's.

**Changes** from `specs-ref`'s `authApplierV3__RoleGet.lean`: the old per-mode chain predicates (`apply.chainRes`, `kvOwnPre`) restated over `applierAt`, `stAt` and `layersStep`

**Margin.** A refused call resets `authInfo` to `""`/`0` (`auth.go:225-226`, `236-237`): `aiAt` comes back at some value.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

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

/-- **`RoleGet` at the authApplierV3 layer**: the layers' step (the result `resMatch`). -/
def authApplierV3.RoleGet.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (u : GoString) (rev : w64) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3.ty) #p) baseLayers b aa ∗
      beAt b mc γ γc R ∗
      stAt b σ ∗
      aiAt aa u rev ∗
      reqMsgAt rq op ∗ ⌜(∃ n, op = .req (.roleGet n)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3.ty @!! go!"RoleGet")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ (∃ u' rv', aiAt aa u' rv') ∗ ∃ σ' res res', ⌜layersStep mc σ u (uint.nat rev) op baseLayers σ' res ∧ resMatch op false res res'⌝ ∗
      stAt b σ' ∗ replyAt γ op res' (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGetResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
