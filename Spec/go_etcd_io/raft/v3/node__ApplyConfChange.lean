/- Lean-first (no Rocq counterpart).

## `node.ApplyConfChange`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `node.ApplyConfChange.specRaw`.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.ApplyConfChange(cc)`** in a static cluster of the voters `vs`, from any goroutine: a
change that keeps the voters and drops only learners (`CCShrink`: e.g. a `ConfChange` with
`NodeId = 0`, or a `RemoveNode` of a learner), which the client states of a change it requested
(its committed requested entries say which). The answer is a fresh `ConfState`: the voters, no
learner among them, not joint; (2026-10-29, stage U9a) or `nil` if the node stopped first
(`nodeStopped`). (2026-10-27: raft's static case, `node__ApplyConfChange.lean`.) -/
abbrev node.ApplyConfChange.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (c : GoInterface) (o : ConfChangeIM),
  CCShrink (GMap.listToSet vs) (ccV2Of o).1 (ccV2Of o).2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
      isStaticCluster γ N vs snapOk ∗ ownConfChangeI c DFrac.discard (some o) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp; (csPts csp (DFrac.own 1) cs true ∗
      ⌜cs.Voters' ≡ₚ vs ∧ (∀ k ∈ cs.Learners', k ∉ vs) ∧ cs.VotersOutgoing' = [] ∧
        cs.LearnersNext' = [] ∧ cs.AutoLeave' = false⌝) ∨
    -- (2026-10-29, stage U9a) the node stopped: `nil`
    (⌜csp = null⌝ ∗ nodeStopped n γ N) }}

/-- **`node.ApplyConfChange(cc)`** in a dynamic cluster, from any goroutine: the change of the next
conf-change entry `e` of the committed log delivered to the node, at position `k` past its view's
configuration index (no conf-change entry between), as the decoder gives it (`o'`), or any change
`o` with its effect on the view's membership (2026-10-29, stage U5: an auto-leave joint configuration
included; until then the result was not left automatically). The view moves past the entry, to the membership the change gives; the answer
is a fresh `ConfState` reporting it. (Today the dynamic case of `node__ApplyConfChange.lean`,
`DynCCPreOp`, `nodeCfg`, `dlvLb`.) -/
abbrev node.ApplyConfChange.dynamicSpec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (c0 : Membership)
    (decode : ConfChangeDecoder) (c : GoInterface) (o o' : ConfChangeIM) (l : List LogEntry)
    (k : Nat) (e : LogEntry) (v : ConfigView) (m' : Membership),
  v.applied ≤ k → l[k]? = some e → e.isConfChange → NoConfChangeIn l v.applied k →
  decode (l.take k) e = some o' → Membership.applyChange o' v.membership = some m' →
  Membership.applyChange o v.membership = some m' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
      isDynamicCluster γ N c0 decode ∗ ownConfChangeI c DFrac.discard (some o) ∗
      nodeConfig n γ N v ∗ deliveredLogLb n γ N l }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp; (csPts csp (DFrac.own 1) cs true ∗
      nodeConfig n γ N ⟨k + 1, m'⟩ ∗ ⌜confStateIs cs m'⌝) ∨
    -- (2026-10-29, stage U9a) the node stopped: `nil`, the view given up
    (⌜csp = null⌝ ∗ nodeStopped n γ N) }}

/-- **`node.ApplyConfChange(cc)` in a cluster with snapshots and reconfiguration** (2026-10-28, stage
U4a; `isCluster`, `InvNodeRule.lean`): as `node.ApplyConfChange.dynamicSpec`, the decoder's change
replaced by the recorded decision (candidate 13's shape): the conf entry at position `k` was decided
to apply `o'` (`confDecided`), and the change `o` handed in has the effect of `o'` at the view's
membership, an auto-leave joint configuration included (2026-10-29, stage U5: until then
`m'.autoLeave = false`, raft's automatic leave being out of `raft.Step`'s scope). (2026-10-28, the conf-change decision switch,
§4) The conf entries between the view and `k` decided `.skip` (`skippedIn`; until then none at all,
`NoConfChangeIn`). -/
abbrev node.ApplyConfChange.unifiedSpec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (c : GoInterface) (o o' : ConfChangeIM)
    (l : List LogEntry) (k : Nat) (e : LogEntry) (v : ConfigView) (m' : Membership),
  v.applied ≤ k → l[k]? = some e → e.isConfChange →
  Membership.applyChange o' v.membership = some m' →
  Membership.applyChange o v.membership = some m' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
      isCluster γ N ∗ confDecided γ k (.apply o') ∗ ownConfChangeI c DFrac.discard (some o) ∗
      nodeConfig n γ N v ∗ deliveredLogLb n γ N l ∗ skippedIn γ l v.applied k }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp; (csPts csp (DFrac.own 1) cs true ∗
      nodeConfig n γ N ⟨k + 1, m'⟩ ∗ ⌜confStateIs cs m'⌝) ∨
    -- (2026-10-29, stage U9a) the node stopped: `nil`, the view given up
    (⌜csp = null⌝ ∗ nodeStopped n γ N) }}

end spec

end EtcdGrove
end Perennial
