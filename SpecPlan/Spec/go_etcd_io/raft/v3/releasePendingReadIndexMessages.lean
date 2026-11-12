/-
## `releasePendingReadIndexMessages(r)` (internal)

**Users.** `stepLeader` (after a commit). **Proof sketch.** None pending: nothing. Else, an entry of
the leader's term committed (`committedEntryInCurrentTerm`, else an error is logged): the pending
reads are answered (`sendMsgReadIndexResponse`: one voter, at once at the commit index, which covers
every entry committed before the read; else registered and confirmed by a heartbeat round).
**Changes** (from `specs-ref`'s `releasePendingReadIndexMessages.lean`): over `raftCore`.
**Margin.** As `bcastHeartbeat`'s.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) A leader answers the reads it postponed. -/
def releasePendingReadIndexMessages.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ ⌜ρ.role = StateLeader⌝ }}
    (App (Val (@! go_etcd_io.raft.v3.releasePendingReadIndexMessages)) (Val #r))
  {{ RET #(); raftCore r γ id ρ }}

end spec
end Raft
end EtcdGrove
end Perennial
