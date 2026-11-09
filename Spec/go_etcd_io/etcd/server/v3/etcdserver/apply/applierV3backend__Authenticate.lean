/-
`(*applierV3backend).Authenticate(r)` (`backend.go:157-164`): the auth store's `Authenticate` with the consistent index and the simple-token prefix in the context.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** `ConsistentIndex()` (`ciOk`, with `R`); 3d's `Authenticate` (the token registered in `γ`: `tokenUser`); `newHeader`.

**Changes** from `specs-ref`'s `applierV3backend__Authenticate.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction

**Margin.** The header's other fields (cluster, member, term, leader) any.
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

/-- **`Authenticate` at the applierV3backend layer**: the layers' step (exact). -/
def applierV3backend.Authenticate.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ n pw t, op = .authenticate n pw t) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"Authenticate")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ ∃ σ' res, ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res⌝ ∗ stAt p σ' ∗
      replyAt γ op res (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
