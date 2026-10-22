/- Lean-first (no Rocq counterpart).

## `setupNode(c, peers)` (node.go:250)

`StartNode`'s body but for the goroutine: `panic` on no peer (excluded: `ps ≠ []`),
`NewRawNode(c)` (panicking on an error, which its spec excludes), `rn.Bootstrap(peers)` (its
error only logged; none under `RawNode.Bootstrap.spec`'s premises) and `newNode(rn)`, returned
by pointer. The premises are `NewRawNode.spec`'s (the conf state empty: a new cluster's) and
`RawNode.Bootstrap.spec`'s (the peers, the bootstrap log, this node's ghost state); the result is
the `node` value at `n` with its channels (`newNodeChans`) over the `RawNode` closed at the
peers' configuration (`ownRawNode`, static, term `1`, nothing delivered), as `StartNode` hands it
to `run` (2026-10-16, stage R8b, D12).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Spec.go_etcd_io.raft.v3.RawNode__Bootstrap
public import Spec.go_etcd_io.raft.v3.newNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev setupNode.spec : Prop :=
  ∀ (γ : RaftNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  -- `NewRawNode`'s premises
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  σ.prev = entryID.mk (W64 0) (W64 0) →
  σ.ents = [] →
  (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] →
  HsEmpty hs →
  -- the conf state empty: a new cluster's
  csm.Voters' = [] →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  -- the peers (`RawNode.Bootstrap`'s premises)
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  γ.reBoot = bootLog →
  BootLogOk γ.reCCOk ps bootLog →
  -- (D19i part 1) the floor not raised yet: the storage's view, fresh to raft
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            R -∗ hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      ownRaftGhost γ cv.ID' (bootPState bootLog) ∗ isCommitted γ bootLog ∗
      -- (2026-10-19, D21 M3) `Bootstrap`'s: in the no-snapshot mode, a storage never compacted
      -- past `1`
      NsCap γ.reNoSnap (interface.ok si) ∗
      -- (D22 S-b′3, 2026-10-20) the storage's certificate link (`certLink`: none needed in the
      -- no-snapshot mode)
      certLink γ (interface.ok si) }}
    (App (App (Val #(functions setupNode [])) (Val #c)) (Val #peers))
  {{ (n : Loc), RET #n;
      R ∗ ∃ (nv : node) (rn : Loc),
        n ↦ nv ∗ ⌜nv.rn' = rn⌝ ∗ newNodeChans nv ∗
        ownRawNode γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 1,
            storage := interface.ok si, mode := RNMode.static,
            cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 } ∗
        peers ↦*{dq} pv }}

end spec

end EtcdGrove
end Perennial
