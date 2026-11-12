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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`mb.MustReadMembersFromBackend()`** (the trust boundary; D43 M5b′, 2026-10-26, the user's
decision; restated 2026-11-01, the backend-auth-split stage): on the membership backend `mb` over
the real backend `d`, with a pooled reader's resource and the caller's
thread token (`backend.bkRPool`, `threadTok`: one read transaction, its slot borrowed and given back)
and **the idle part of the membership buckets** at `bk` (`rbOwnIn d.γB membership.memberBkts bk`),
which are as the apply thread writes them (`membership.membersDecode bk`: members' keys to members'
encodings, removed members' keys), it returns the members' map and the removed map they decode to
(`membersOfBk bk`: the members' records with their peer URLs, `membersRead`, and the removed ids).
Go (`schema/membership.go:83-122`): `readMembersFromBackend` reads both buckets through
`be.ReadTx()` (`RLock`, two `UnsafeForEach`, `RUnlock`), which sees the idle part's contents (the
file header's Go basis: no write to them since the holder's last `Unlock`); every key parses
(`mustParseMemberIDFromBytes` of `BackendMemberKey`'s hex) and every value unmarshals to a non-nil
member (`json.Marshal` of a `*Member` is a JSON object), so no `lg.Panic` and a record per key.
(Until 2026-11-01 the pre took the writer's half `rbOwn d.γB bk`, the store's reader token and no
decoding premise, which made it false: a caller inside a batch with a pending delete of a member
reads the old member, `TestBksReadInsidePendingBatch`; an undecodable key panics,
`TestBksReadUndecodableMember`; a `null` value gives a nil member, `TestReview5NullMemberValue`;
all in `examples/axiomcx/backend-auth-split/`.) -/
abbrev schema.membershipBackend.MustReadMembersFromBackend.spec : Prop :=
  ∀ (mb lg : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (bk : GMap GoString backend.BktData),
  membership.membersDecode bk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schema.mbF go!"be" mb ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      schema.mbF go!"lg" mb ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ backend.isBackend d.γB d.P W Pk d.be ∗
      backend.bkRPool d.γB d.P d.be ∗ threadTok ∗
      backend.rbOwnIn d.γB membership.memberBkts bk }}
    (App (Val (mb @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!!
      go!"MustReadMembersFromBackend")) (Val #()))
  {{ (mp rp : Loc), RET (PairV #mp #rp); backend.bkRPool d.γB d.P d.be ∗ threadTok ∗
      backend.rbOwnIn d.γB membership.memberBkts bk ∗
      membership.membersRead mp (membership.membersOfBk bk).1 ∗
      rp ↦$ (membership.membersOfBk bk).2 }}


end spec

end EtcdGrove
end Perennial
