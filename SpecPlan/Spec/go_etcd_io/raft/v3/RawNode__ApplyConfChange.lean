/-
## `RawNode.ApplyConfChange(cc)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** As `node.ApplyConfChange.spec`'s, synchronously. **Changes.** As
`node.ApplyConfChange`'s. Verify-round (A5 completeness F2, raft-conf-pb's request): `confStateFull` (Go's `ConfState()` sets `AutoLeave`), so the server can store it in a snapshot (`CreateSnapshot`, the merged `MsgSnap`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
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
variable [ctx_sem : context.Assumptions]

/-- `RawNode.ApplyConfChange`, as `node.ApplyConfChange` (never `nil`). -/
def RawNode.ApplyConfChange.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (ph : Nat) (adv : Bool) (cc : GoInterface) (dq : DFrac) (c : ConfChangeI)
    (v : ConfView) (l : List LogEntry) (k : Nat) (m' : Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id ph adv ∗ confChangePts cc dq c ∗ nodeConf rn γ v ∗ deliveredLb rn γ l ∗
      confDecided γ k (.apply c) ∗
      ⌜(∃ e, l[k]? = some e ∧ e.isConfChange) ∧ Membership.applyChange c v.membership = some m'⌝ ∗
      (if v.applied ≤ k then confSkipped γ l v.applied k else iprop(⌜m' = v.membership⌝)) }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"ApplyConfChange")) (Val #cc))
  {{ (csp : Loc), RET #csp; ∃ cs, rawNodeAt rn γ id ph adv ∗ confChangePts cc dq c ∗
      RaftPb.confStateFull csp (DFrac.own 1) cs ∗ ⌜cs.Is m'⌝ ∗
      nodeConf rn γ (if v.applied ≤ k then ⟨k + 1, m'⟩ else v) }}

end spec
end Raft
end EtcdGrove
end Perennial
