/-
## `raft.campaign(t)` (internal)

**Users.** `hup` (`raft.go:1007`, after its checks), `stepCandidate` (`raft.go:1717`: a won pre-vote,
`campaignElection`). **Proof sketch.** `becomePreCandidate` (pre-election: the vote requests for the
next term) or `becomeCandidate`; the voters' ids sorted (R4's `Voters.IDs`, `slices.Sort`); for
itself, a vote response to itself (`send`: queued after the append, acknowledged at `Advance`); for
each other voter, a vote request with its last entry id (R3's `lastEntryID`) and, for a transfer,
the context `CampaignTransfer` (`send`; its `msgJust`: the candidate's term and log). **Changes**
(from `specs-ref`'s `raft__campaign.lean`): over the opened struct, the guard named. **Margin.**
Says nothing of the new view but the invariant.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Starts a (pre-)campaign of type `t`, under `hup`'s guard or after a won pre-vote. -/
def raft.campaign.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ ⌜o.view.role ≠ StateLeader ∧
      (CampaignGuard id o ∨ (o.view.role = StatePreCandidate ∧
        #t = go_etcd_io.raft.v3.campaignElection))⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"campaign")) (Val #t))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗ coreInv r γ id o' }}

end spec
end Raft
end EtcdGrove
end Perennial
