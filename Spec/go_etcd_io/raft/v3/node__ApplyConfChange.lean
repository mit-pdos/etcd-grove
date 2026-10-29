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

/-- **`node.ApplyConfChange(cc)` in a cluster with snapshots and reconfiguration** (2026-10-28, stage
U4a; `isCluster`, `InvNodeRule.lean`): as `node.ApplyConfChange.dynamicSpec`, the decoder's change
replaced by the recorded decision (candidate 13's shape): the conf entry at position `k` was decided
to apply `o'` (`confDecided`), and the change `o` handed in has the effect of `o'` at the view's
membership, an auto-leave joint configuration included (2026-10-29, stage U5: until then
`m'.autoLeave = false`, raft's automatic leave being out of `raft.Step`'s scope). (2026-10-28, the conf-change decision switch,
§4) The conf entries between the view and `k` decided `.skip` (`skippedIn`; until then none at all,
`NoConfChangeIn`). -/
abbrev node.ApplyConfChange.spec : Prop :=
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
