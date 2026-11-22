/-
`(*membershipBackend).MustDeleteMemberFromBackend(id)` (`membership.go`): the member backend's delete
(D43 M5b′, 2026-10-26, the user's decision: a contract axiom over the tracked buckets, not proved
through the batch lock's hook; since 2026-11-22, prove-ps2-members, translated with its body and
proved over the backend's specs). Lean-first (no Rocq counterpart).
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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`mb.MustDeleteMemberFromBackend(id)`** (the trust boundary; D43 M5b′, 2026-10-26, the
user's decision): as `MustSaveMemberToBackend`'s contract (the membership backend `mb` over the
real backend `d`, its ghost names pinned by `isBackend d.γB …`, the caller's critical-section
contract, a write session's token spent, the reader's token lent), it deletes `members/<id>` and
puts `members_removed/<id> := "removed"` (`memberKey`, `removedVal`) in a part of any bucket set
`S` containing both (`rbPart d.γB S`: `bk` to `bkPut (bkDel bk …) …`), which comes back **idle**
(`rbOwnIn d.γB S`: the delete is pending at its `Unlock`, which commits it, and writes the put
back, the Go basis: `TestBksDeleteThenRead`; 2026-11-01, the backend-auth-split stage: until then
the whole writer's half `rbOwn`), and returns `Post`. Both buckets exist (`UnsafeDelete`/
`UnsafePut` on a missing bucket is fatal). (R8, 2026-11-07: restated over mvcc's API, the same
meaning, as `MustSaveMemberToBackend`'s.) (prove-ps2-members, 2026-11-22, when it was proved) Both
buckets are in the backend's table (`d.P.has`: what the backend's `UnsafeDelete`/`UnsafePut` take, so
that they are among its ghost names; the server's backends' parameters, `bootOk`'s, the user's approval
of 2026-11-22); until then not a premise of the axiom. -/
abbrev schema.membershipBackend.MustDeleteMemberFromBackend.spec : Prop :=
  ∀ (mb lg : Loc) (d : mvcc.KBReal) (P : IProp GF) (f : GoFunc)
    (Pre Q Post : IProp GF) (S : GoString → Prop) (bk : GMap GoString backend.BktData) (id : w64)
    (W : IProp GF),
  (∀ n, membership.memberBkts n → S n) →
  (bk.lookup go!"members").isSome → (bk.lookup go!"members_removed").isSome →
  d.P.has mvcc.membersBI → d.P.has mvcc.membersRemovedBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schema.mbF go!"be" mb ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      schema.mbF go!"lg" mb ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      backend.plHookRO d.γB f ∗ ⌜f ≠ func.nil⌝ ∗ srvApi.csContractA P f Pre Q Post ∗
      apply.bkWT d ∗ apply.bkRT d ∗
      backend.isBackend d.γB d.P W P d.be ∗ backend.rbPart d.γB S bk }}
    (App (Val (mb @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!!
      go!"MustDeleteMemberFromBackend")) (Val #id))
  {{ RET #(); Post ∗ apply.bkRT d ∗
      backend.rbOwnIn d.γB S
        (apply.bkPut (apply.bkDel bk go!"members" (apply.memberKey id))
          go!"members_removed" (apply.memberKey id) membership.removedVal) }}


end spec

end EtcdGrove
end Perennial
