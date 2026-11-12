/-
`(*applierV3backend).UserChangePassword(r)` (`backend.go:182-188`): the auth store's `UserChangePassword`.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 3d's `authStore.UserChangePassword` (an `Auth.AdminTriple` at the writer's `Auth.authCur γa i a`,
`a = σ.auth`, from `stAt`'s `authSt`; the request `Auth.authReqAt r rq cred` from `reqMsgAt`, with
`cred` the op's credential): its premises `authReached γ (storeNext rq cred a)` and `recordsFit`
from `nextOk` (the step's next state, `opStep`'s realization: `σ'.auth = storeNext rq cred a`);
`authSt`'s `Auth.authBeCur γa abe` and the backend's post-lock hook `Auth.authBeHook abe R Q`
(`hooksOk`'s producer at `authSt`'s wrapper `abe`), passed straight to the triple; its post
`admStep`, the writer at `i + 1`, `authBeCur` back, and `hookOut abe R Q` (`Q`, or `R` with the
unused hook), which `hooksOk`'s `□ (Q ={⊤}=∗ R)` turns into `R`;
`newHeader`.

**Changes** from `specs-ref`'s `applierV3backend__UserChangePassword.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction
verify-round (A9 F3, F6; re-review A9 N1): the auth store's hook has a source, `beAt`'s `optsOk`'s
`hooksOk` (`Auth.authBeHook abe R Q`) with `authSt`'s `Auth.authBeCur γa abe`, which 3d's
`AdminTriple` now takes directly (its `authHook`/`authHook_intro` are gone); the statement is
unchanged.

**Margin.** The header's other fields (cluster, member, term, leader) any.

**Integration (I5).** Takes `nextOk` (the next state's auth reached and fitting; for `Authenticate`
the token index), which 3d's `AdminTriple`/`Authenticate` need; the apply thread (2d) supplies it.
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

/-- **`UserChangePassword` at the applierV3backend layer**: the layers' step (exact). -/
def applierV3backend.UserChangePassword.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ n h, op = .userChangePassword n h) ∧ op.ok⌝ ∗
      nextOk γ R op (fun σ' => ∃ res, layersStep mc σ [] 0 op [Layer.backend] σ' res) ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"UserChangePassword")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ ∃ σ' res, ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res⌝ ∗ stAt p σ' ∗
      replyAt γ op res (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserChangePasswordResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
