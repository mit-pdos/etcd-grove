/-
## `raft.applyConfChange(cc)`

**Users.** `RawNode.ApplyConfChange` (`rawnode.go:121`, with `cc.AsV2()`); `node.run`'s `confc` arm
(`node.go:399`, the `ConfChangeV2` `node.ApplyConfChange` sent). R1's `RawNode.ApplyConfChange.spec`
and `node.ApplyConfChange.spec` take the same premises over the client's `ConfChangeI` `c`; `c2` is
its `AsV2()` (3h's law: `applyChange (.v2 c.AsV2) = applyChange c`). Snippet: `conf.go`.

**Proof sketch.** confchange's `Changer` (R4) on the tracker, by the transition: `LeaveJoint`,
`EnterJoint`, `Simple`; it succeeds (`Membership.applyChange c v.membership = some m'`), so no panic;
`switchToConfig` (the tracker at `m'`; a removed or demoted leader steps down with
`stepDownOnRemoval`; a leader commits what the new quorum allows, `maybeCommit`, and probes the new
peers; the transfer aborted if its target left). The view: the decision `confDecided γ k (.apply c)`
on the delivered conf entry `k` and the skipped ones before it give `confAt γ (k+1) m'`
(`confAt_skipped`, `confAt_decided`), which the node's tracker now holds (`nodeConf rn γ ⟨k+1, m'⟩`);
an entry below the view changes nothing (`m' = v.membership`).

**Changes** (from `specs-ref`'s `raft__applyConfChange.lean`): over R1's view and decisions (was
`ccOk`/`CCApply` over the tracker's record).

**Margin.** The returned `ConfState` is fresh; nothing is said of the new view `ρ'`.
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

/-- **Applies conf change `c2`** (decided `c` for delivered entry `k`) to node `id`'s tracker: the configuration `m'`, the view past the entry. -/
def raft.applyConfChange.spec : Prop :=
  ∀ (r rn : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (p : Loc) (dq : DFrac)
    (c2 : ConfChangeV2) (c : ConfChangeI) (v : ConfView) (l : List LogEntry) (k : Nat)
    (m' : Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ raftOf rn r ∗ confChangePts (interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChangeV2.ty) #p) dq (.v2 c2) ∗
      nodeConf rn γ v ∗ deliveredLb rn γ l ∗ confDecided γ k (.apply c) ∗
      ⌜(∀ mm, Membership.applyChange (.v2 c2) mm = Membership.applyChange c mm) ∧
        (∃ e, l[k]? = some e ∧ e.isConfChange) ∧ Membership.applyChange c v.membership = some m'⌝ ∗
      (if v.applied ≤ k then confSkipped γ l v.applied k else iprop(⌜m' = v.membership⌝)) }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"applyConfChange")) (Val #p))
  {{ (csp : Loc), RET #csp; ∃ (ρ' : CoreView) (cs : ConfState), raftCore r γ id ρ' ∗
      confChangePts (interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChangeV2.ty) #p) dq (.v2 c2) ∗ confStatePts csp (DFrac.own 1) cs ∗ ⌜cs.Is m'⌝ ∗
      nodeConf rn γ (if v.applied ≤ k then ⟨k + 1, m'⟩ else v) }}

end spec
end Raft
end EtcdGrove
end Perennial
