/-
## `(*membershipBackend).MustSaveMemberToBackend(p)`: assumed (names only)

**Users.** `RaftCluster.AddMember`, `UpdateAttributes`, `PromoteMember`, `UpdateRaftAttributes` with `shouldApplyV3` (2e). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `BackendMemberKey(m.ID)`, `json.Marshal(m)` (strings, `uint64`s, `bool`s: no error, `lg.Panic` unreachable), `be.BatchTx()`, `LockInsideApply()` (`applyHook`), `UnsafePut(Members, key, json)`, `Unlock()`. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__MustSaveMemberToBackend.lean` where there was one (over the real
backend's ghost names): over the schema's `memberBkts`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **Stores the member** (the post-lock hook run). -/
def membershipBackend.MustSaveMemberToBackend.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : ClusterBkts) (p : Loc) (dq : DFrac) (mm : EtcdModel.Member) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ Zap.isLogger lg ∗ memberBkts be (some cb) ∗ Membership.memberPts p dq mm ∗ applyHook be Pre Q ∗ Pre }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustSaveMemberToBackend")) (Val #p))
  {{ RET #(); memberBkts be (some { cb with st := cb.st.add mm }) ∗ Membership.memberPts p dq mm ∗ Q }}

end spec
end Schema
end EtcdGrove
end Perennial
