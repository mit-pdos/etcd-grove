/- Lean-first (no Rocq counterpart).

## `node.Advance`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `node.Advance.specRaw`.)
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

/-- **`node.Advance()` in a cluster with snapshots and reconfiguration** (2026-10-28, stage U4a;
`isCluster`, `InvNodeRule.lean`): the driver, done with a `Ready`, hands it back; the loop is idle
again; (2026-10-29, stage U9a) or the node stopped first (`nodeStopped`), the loop idle as well,
nothing else promised. Premises of the snapshot path, all of what the client has from the `Ready`
(`readySnap`): the snapshot's certificate and its index the length of its committed log. Every conf
entry of the committed log delivered is applied (the loop's A1 at `run`'s `RawNode.Advance`; the
conf-change decision switch: or decided `.skip`, `skippedIn`; raft-final, 2026-10-29, the design's
A1: after a `Ready` without a snapshot only).

(U8 v2, 2026-10-29, the frozen design's §3) The storage part: the `Ready`'s batch back
(`advReceipt`: a frozen prefix within the committed log delivered and an owned rest, with the end;
nothing for no entries), or after a snapshot `Ready` the storage compacted at the snapshot with its
dummy and the batch after it (`snapReceipt`); the post: raft's applied index has reached the
committed log delivered (`nodeAppliedLb`, the snapshot's index after a snapshot `Ready`). (Until U8
v2 the old contract's receipts and `storFloor`/`storTermsAt`; until then also the static cluster's
`node.Advance.spec` and the dynamic one's `node.Advance.dynamicSpec`, dropped in U8 v2 ahead of U9.) -/
abbrev node.Advance.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState) (es : List EntryM)
    (L : Option SnapLoan) (v : ConfigView),
  st.handling = some (es, L) →
  (∀ l, L = some l → l.dlv.length = uint.nat l.snap.Metadata'.Index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isCluster γ N ∗ isNode n γ N id ∗
      nodeDriver n γ N st ∗ advReceipt st.storage st.delivered.length es L ∗ nodeConfig n γ N v ∗
      -- (raft-final, 2026-10-29, the design's A1, review 1's H1) the conf entries skipped only after a
      -- `Ready` without a snapshot (after one, the configuration is the snapshot's, `confAt`); until
      -- then after both
      (match L with
       | none => skippedIn γ st.delivered v.applied st.delivered.length
       | some l => snapshotCert γ N (snapTrip l.snap l.snap.Metadata'.ConfState'.lists)) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); (nodeDriver n γ N { st with handling := none } ∗
      nodeAppliedLb γ id st.delivered.length ∗
      match L with
      | none => nodeConfig n γ N v
      | some l => ∃ m : Membership,
          nodeConfig n γ N ⟨uint.nat l.snap.Metadata'.Index', m⟩ ∗
          confAt γ (uint.nat l.snap.Metadata'.Index') m ∗
          ⌜confStateIs l.snap.Metadata'.ConfState' m⌝) ∨
    -- (2026-10-29, stage U9a) the node stopped: the loop idle again
    (nodeStopped n γ N ∗ nodeDriver n γ N { st with handling := none }) }}

end spec

end EtcdGrove
end Perennial
