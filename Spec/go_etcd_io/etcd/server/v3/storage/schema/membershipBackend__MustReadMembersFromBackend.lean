/-
`(*membershipBackend).MustReadMembersFromBackend()` (`membership.go`): the trust boundary for the
member backend's read (D43 M5b′, 2026-10-26, the user's decision: a contract axiom over the
tracked buckets; until then `ValidateConfigurationChange`'s verdict was opaque, `ccValidOn`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustSaveMemberToBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`mb.MustReadMembersFromBackend()`** (the trust boundary; D43 M5b′, 2026-10-26, the user's
decision): on the membership backend `mb` over the real backend `d` of the store's names `γ`, with
the reader's token (lent) and the writer's half of the tracked buckets at `bk` (read only: a read
transaction sees what the last `Unlock` wrote back, and the tracked buckets' writer, the caller,
holds no batch lock), it returns the members' map and the removed map the `members` and
`members_removed` buckets decode to (`membersOfBk bk`: the members' records with their peer URLs,
`membersRead`, and the removed ids). -/
abbrev schema.membershipBackend.MustReadMembersFromBackend.spec : Prop :=
  ∀ (mb lg : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (bk : GMap GoString backend.BktData),
  γ.kb = some d →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schema.mbF go!"be" mb ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      schema.mbF go!"lg" mb ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ mvcc.storeRT γ ∗ backend.rbOwn d.γB bk }}
    (App (Val (mb @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!!
      go!"MustReadMembersFromBackend")) (Val #()))
  {{ (mp rp : Loc), RET (PairV #mp #rp); mvcc.storeRT γ ∗ backend.rbOwn d.γB bk ∗
      membership.membersRead mp (membership.membersOfBk bk).1 ∗
      rp ↦$ (membership.membersOfBk bk).2 }}

end spec

end EtcdGrove
end Perennial
