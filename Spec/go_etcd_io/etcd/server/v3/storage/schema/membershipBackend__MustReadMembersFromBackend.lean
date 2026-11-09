/-
## `(*membershipBackend).MustReadMembersFromBackend()`: assumed (names only)

**Users.** Bootstrap (`bootstrap.go:133`), `RaftCluster.Recover`, `ValidateConfigurationChange` (2e). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `be.ReadTx()`, `RLock()` (a reader slot: the caller's thread token), two `UnsafeForEach` (an absent bucket: nothing; each key parses as a member id: the keys are `BackendMemberKey`'s; each value unmarshals to a member, `json.Marshal`'s output), `RUnlock()`; `lg.Panic` unreachable. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__MustReadMembersFromBackend.lean` where there was one (over the real
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

/-- **The members and the removed ids**, as fresh maps (empty if the buckets are absent). -/
def membershipBackend.MustReadMembersFromBackend.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : Option ClusterBkts),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ Zap.isLogger lg ∗ memberBkts be cb ∗ threadTok }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustReadMembersFromBackend")) (Val #()))
  {{ (mp rp : GoMap), RET (PairV #mp #rp); memberBkts be cb ∗ threadTok ∗ ∃ (M : GMap w64 Loc) (Rm : GMap w64 Bool), mp ↦$ M ∗ rp ↦$ Rm ∗ ⌜(∀ id, (Rm !! id = some true ↔ uint.nat id ∈ (cb.getD ClusterBkts.empty).st.removed) ∧ (Rm !! id ≠ some false)) ∧ (∀ mm ∈ (cb.getD ClusterBkts.empty).st.members, ∃ id, uint.nat id = mm.id ∧ M !! id ≠ none)⌝ ∗ [∗map] id ↦ p ∈ M, ∃ mm, ⌜mm ∈ (cb.getD ClusterBkts.empty).st.members ∧ mm.id = uint.nat id⌝ ∗ Membership.memberPts p (DFrac.own 1) mm }}

end spec
end Schema
end EtcdGrove
end Perennial
