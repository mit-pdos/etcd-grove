/-
## `(*membershipBackend).MustDeleteMemberFromBackend(id)`: assumed (names only)

**Users.** `RaftCluster.RemoveMember` with `shouldApplyV3` (2e). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `BackendMemberKey(id)`, `be.BatchTx()`, `LockInsideApply()` (`applyHook`), `UnsafeDelete(Members, key)`, `UnsafePut(MembersRemoved, key, "removed")`, `Unlock()`. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__MustDeleteMemberFromBackend.lean` where there was one (over the real
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

/-- **Removes the member, recording it as removed** (the post-lock hook run). -/
def membershipBackend.MustDeleteMemberFromBackend.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : ClusterBkts) (id : w64) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ memberBkts be (some cb) ∗ applyHook be Pre Q ∗ Pre }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustDeleteMemberFromBackend")) (Val #id))
  {{ RET #(); memberBkts be (some { cb with st := cb.st.remove (uint.nat id) }) ∗ Q }}

end spec
end Schema
end EtcdGrove
end Perennial
