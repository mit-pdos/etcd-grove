/-
## `raft.becomePreCandidate()` (internal)

**Users.** `campaign` (`raft.go:1052`). **Proof sketch.** Not a leader (`raft.go:937`); the step
function and tick of a candidate, the votes reset (R4), no leader, the role; the term and vote kept.
The invariant: a pre-candidate holds `hup`'s guard (`CampaignGuard`) while it stays one.
**Changes** (from `specs-ref`'s `raft__becomePreCandidate.lean`): over the opened struct.
**Margin.** Exact on the view.
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

/-- (internal) Becomes a pre-candidate (term and vote kept). -/
def raft.becomePreCandidate.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ ⌜o.view.role ≠ StateLeader ∧ CampaignGuard id o⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"becomePreCandidate")) (Val #()))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗ coreInv r γ id o' ∗
      ⌜o'.view = { o.view with lead := W64 0, role := StatePreCandidate } ∧ o'.log = o.log⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
