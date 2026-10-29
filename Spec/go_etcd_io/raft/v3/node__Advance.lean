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

/-- (open) **`node.Advance()`**: the driver, done with a `Ready` (its entries `es` appended, or its
snapshot installed: the storage contract's receipt, `advReceipt`), hands it back; the loop is idle
again. After a `Ready` without a snapshot, the storage's floor is at least the committed log
delivered (`storFloor`, today `reqWit`). (2026-10-27: the premise that no conf-change entry was
delivered is gone: the nodes are in raft's static mode, which needs none -- a conf change the client
applies keeps the voters, `node.ApplyConfChange`. For etcd's server: in a static cluster,
`isStaticCluster`; a dynamic cluster's is `node.Advance.dynamicSpec`.) -/
abbrev node.Advance.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (st : NodeDriverState) (es : List EntryM)
    (L : Option SnapLoan),
  st.handling = some (es, L) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isStaticCluster γ N vs snapOk ∗
      nodeDriver n γ N st ∗ advReceipt st.storage es L }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriver n γ N { st with handling := none } ∗
      match L with
      | none => ∃ x : w64, storFloor st.storage x ∗ ⌜(st.delivered.length : Int) ≤ uint.Z x⌝
      | some _ => True }}

/-- **`node.Advance()`** in a dynamic cluster: as `node.Advance.spec`, if every conf-change entry
of the committed log delivered is applied (none past the view's configuration index:
`issues/raft-advance-before-applyconfchange.md`, today's A1). After a `Ready` without a snapshot the
view is unchanged; (2026-10-28, stage U3d, the frozen design's `node.Advance`) after one with a
snapshot (its loan `l`) the view is at the snapshot's index and a membership its `ConfState` reports.
(A dynamic cluster is in raft's no-snapshot mode, so the second case does not arise yet.) -/
abbrev node.Advance.dynamicSpec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (c0 : Membership) (decode : ConfChangeDecoder)
    (st : NodeDriverState) (es : List EntryM) (L : Option SnapLoan) (v : ConfigView),
  st.handling = some (es, L) →
  NoConfChangeIn st.delivered v.applied st.delivered.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isDynamicCluster γ N c0 decode ∗
      nodeDriver n γ N st ∗ advReceipt st.storage es L ∗ nodeConfig n γ N v }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriver n γ N { st with handling := none } ∗
      match L with
      | none => nodeConfig n γ N v ∗
          ∃ x : w64, storFloor st.storage x ∗ ⌜(st.delivered.length : Int) ≤ uint.Z x⌝
      | some l => ∃ m : Membership,
          nodeConfig n γ N ⟨uint.nat l.snap.Metadata'.Index', m⟩ ∗
          ⌜confStateIs l.snap.Metadata'.ConfState' m⌝ }}

/-- **`node.Advance()` in a cluster with snapshots and reconfiguration** (2026-10-28, stage U4a;
`isCluster`, `InvNodeRule.lean`): as `node.Advance.dynamicSpec`, with the snapshot path reachable.
After a `Ready` with a snapshot (its loan `l`), the view is at the snapshot's index and the membership
`m` after the committed log up to it (`confAt`), which its `ConfState` reports; after one without,
the storage's floor and (2026-10-28) its terms of the committed log delivered (`storTermsAt`), also
when a snapshot was restored since. Premises of the
snapshot path, all of what the client has from the `Ready` (`readySnap`): the snapshot's
certificate and its index the length of its committed log (until 2026-10-29, stage U5, also its
`ConfState` no auto-leave one, as `RawNode.Advance`'s). (As `node.Advance.dynamicSpec`, every conf entry of the
committed log delivered is applied, after a snapshot `Ready` too: the loop's A1 at `run`'s
`RawNode.Advance`, over the snapshot's committed log; 2026-10-28, the conf-change decision switch,
§4: or decided `.skip`, `skippedIn`, until then `NoConfChangeIn`.) -/
abbrev node.Advance.unifiedSpec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) (es : List EntryM)
    (L : Option SnapLoan) (v : ConfigView),
  st.handling = some (es, L) →
  (∀ l, L = some l → l.dlv.length = uint.nat l.snap.Metadata'.Index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isCluster γ N ∗
      nodeDriver n γ N st ∗ advReceipt st.storage es L ∗ nodeConfig n γ N v ∗
      skippedIn γ st.delivered v.applied st.delivered.length ∗
      (match L with
       | none => True
       | some l => snapshotCert γ N (snapTrip l.snap l.snap.Metadata'.ConfState'.lists)) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriver n γ N { st with handling := none } ∗
      match L with
      | none => nodeConfig n γ N v ∗
          ∃ x : w64, storFloor st.storage x ∗ ⌜(st.delivered.length : Int) ≤ uint.Z x⌝ ∗
            -- (2026-10-28, stage U4a) and the storage's terms of the committed log delivered
            -- (what `MemoryStorage.CreateSnapshot.unifiedSpec` takes, `memTermsAt`)
            storTermsAt st.storage (st.delivered.map LogEntry.term)
      | some l => ∃ m : Membership,
          nodeConfig n γ N ⟨uint.nat l.snap.Metadata'.Index', m⟩ ∗
          confAt γ (uint.nat l.snap.Metadata'.Index') m ∗
          ⌜confStateIs l.snap.Metadata'.ConfState' m⌝ }}

end spec

end EtcdGrove
end Perennial
