/-
## `node.ApplyConfChange(cc)`

**Users.** etcd's `EtcdServer.applyConfChange` (`server.go:2037`, `2053`: the entry's change, or the
change with `NodeId = 0` when the server refuses it: a no-op; not called for an entry replayed below
the consistent index); the examples' `Replica.applyConfChange` (`kvdurable/kv.go:700`: v1 and v2,
joint enter and leave, or skipped: refused by not calling). Snippet: `confchange.go`
(`ReqApplyOrRefuse`).

**Proof sketch.** `cc.AsV2()` (raftpb, 3h); send on `confc`; the run goroutine's
`raft.applyConfChange` (R2, over confchange's `Changer`, R4: `Membership.applyChange c` is `some m'`,
so no panic) switches the tracker; the configuration after entry `k` is `m'` (`confAt_decided` from
`confAt γ v.applied` and the skipped entries between); the `ConfState` comes back on `confstatec`.
An entry below the view (re-delivered after a restart or a bootstrap) is applied only when it changes
nothing.

**Changes.** The second case (an entry below the view, a no-op) is new: it replaces the bootstrap
log's special configuration and the restart's skip rule.

**Margin.** After a stop, `nil`. Verify-round (A5 completeness F2, raft-conf-pb's request): `confStateFull` (Go's `ConfState()` sets `AutoLeave`), so the server can store it in a snapshot (`CreateSnapshot`, the merged `MsgSnap`).
-/
module

public import Spec.go_etcd_io.raft.v3.Api

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

/-- **Applies conf change `c`, decided for the committed entry at position `k`**: the view moves past
it (or stays, for an entry already reflected, whose change is then a no-op). Returns the new
configuration (`nil` if the node stopped). -/
def node.ApplyConfChange.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (cc : GoInterface) (dq : DFrac) (c : ConfChangeI)
    (v : ConfView) (l : List LogEntry) (k : Nat) (m' : Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ confChangePts cc dq c ∗ nodeConf n γ v ∗ deliveredLb n γ l ∗ confDecided γ k (.apply c) ∗
      ⌜(∃ e, l[k]? = some e ∧ e.isConfChange) ∧ Membership.applyChange c v.membership = some m'⌝ ∗
      (if v.applied ≤ k then confSkipped γ l v.applied k else iprop(⌜m' = v.membership⌝)) }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"ApplyConfChange")) (Val #cc))
  {{ (csp : Loc), RET #csp; confChangePts cc dq c ∗
      ((∃ cs, RaftPb.confStateFull csp (DFrac.own 1) cs ∗ ⌜cs.Is m'⌝ ∗
          nodeConf n γ (if v.applied ≤ k then ⟨k + 1, m'⟩ else v)) ∨ (⌜csp = null⌝ ∗ nodeStopped n ∗ nodeConf n γ v)) }}

end spec
end Raft
end EtcdGrove
end Perennial
