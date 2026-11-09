/-
## `raft.hup(t)` (internal)

**Users.** `raft.Step` (`MsgHup`: pre-election or election), `stepFollower` (`MsgTimeoutNow`:
transfer). **Proof sketch.** Not a leader, promotable, no unapplied conf entry (`promotable`,
`hasUnappliedConfChanges`): the guard under which `campaign` (pre-candidate, or candidate at the
next term: a receipt) keeps the cluster invariant; else nothing. **Changes** (from `specs-ref`'s
`raft__hup.lean`): over `raftCore` (was `HupGuard`/`HupFact` over `NState`). **Margin.** Says nothing
of the new view. Verify-round (A4 P3): takes and gives the struct's idle token `coreIdle` (it may campaign: `hup`'s scan of `(applied, committed]` needs the published floor at most `applied`, `coreIdle_floor`).
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

/-- (internal) Starts a campaign of type `t` if the node may. -/
def raft.hup.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ coreIdle r }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"hup")) (Val #t))
  {{ RET #(); ∃ ρ', raftCore r γ id ρ' ∗ coreIdle r }}

end spec
end Raft
end EtcdGrove
end Perennial
