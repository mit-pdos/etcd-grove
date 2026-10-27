/-
`(*membershipBackend).MustSaveMemberToBackend(m)` (`membership.go`): the trust boundary for the
member backend's save (D43 M5b′, 2026-10-26, the user's decision: a contract axiom over the
tracked buckets, not proved through the batch lock's hook). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of the membership backend `*membershipBackend` `mb`. -/
abbrev schema.mbF (n : GoString) (mb : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend n mb

end addrs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`mb.MustSaveMemberToBackend(m)`** (the trust boundary; D43 M5b′, 2026-10-26, the user's
decision): on the membership backend `mb` over the real backend `d` of the store's names `γ`
(`mb.be`, `mb.lg` read-only), under the caller's critical-section contract at the store's batch lock
`P` and post-lock hook `f` (`mvcc.hookOk`: `P` and `f` are the backend's; `csContract`, as the
cluster's other writers', `apply.isCluster`), a write session's token (spent: the `Unlock`'s
write-back) and the reader's token (lent), it puts the member `m` (owned, read: `json.Marshal`) as
`members/<id> := json(m)` (`memberKey`, `memberEnc` of its value `mm`) into the tracked buckets
(`rbOwn`, the writer's half: `bk` to `bkPut bk …`) and returns `Post`. The `members` bucket exists
(`UnsafePut` into a missing bucket is fatal). -/
abbrev schema.membershipBackend.MustSaveMemberToBackend.spec : Prop :=
  ∀ (mb lg : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (bk : GMap GoString backend.BktData) (m : Loc) (mm : apply.MemberM),
  γ.kb = some d → (bk.lookup go!"members").isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schema.mbF go!"be" mb ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      schema.mbF go!"lg" mb ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      mvcc.hookOk γ P f ∗ mvcc.csContract P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗
      backend.rbOwn d.γB bk ∗ membership.memberAt m 1 mm }}
    (App (Val (mb @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!!
      go!"MustSaveMemberToBackend")) (Val #m))
  {{ RET #(); Post ∗ mvcc.storeRT γ ∗
      backend.rbOwn d.γB (apply.bkPut bk go!"members" (apply.memberKey mm.id) (apply.memberEnc mm)) ∗
      membership.memberAt m 1 mm }}

end spec

end EtcdGrove
end Perennial
