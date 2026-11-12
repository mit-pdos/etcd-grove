/- Lean-first (no Rocq counterpart).

## `setupNode(c, peers)` (node.go:250)

`StartNode`'s body but for the goroutine: `panic` on no peer (excluded: `ps ≠ []`),
`NewRawNode(c)` (panicking on an error, which its spec excludes), `rn.Bootstrap(peers)` (its
error only logged; none under `RawNode.Bootstrap.spec`'s premises) and `newNode(rn)`, returned
by pointer. The premises are `NewRawNode.spec`'s (its boot bundle: the storage's `FirstIndex`,
`LastIndex` and `InitialState`, at the empty conf state, a new cluster's) and
`RawNode.Bootstrap.spec`'s (the peers, the bootstrap log, this node's ghost state); the result is
the `node` value at `n` with its channels (`newNodeChans`) over the `RawNode` closed at the peers'
configuration (`ownRawNode`, in the mode `md`, term `1`, nothing delivered), as `StartNode` hands it
to `run` (2026-10-16, stage R8b, D12; 2026-10-30, stage R5: restored over the boot bundle, after
U9 deleted it with `StartNode`'s spec).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Spec.go_etcd_io.raft.v3.RawNode__Bootstrap
public import Spec.go_etcd_io.raft.v3.newNode
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange

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

/-- See the file header. (2026-11-12, trace-check step 5) Both modes: `TraceLoggerOk` and `γ.reTrace = none` replaced by the capability's start (`trCapStart`) and, traced, pre-vote and check-quorum off with fewer than `2^40` peers; `trNoCut` in the `InitialState` answer; the completion witness out. -/
abbrev setupNode.spec : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (sn : StorNames) (σ : StorState) (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
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
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → σ.pend = [] →
  σ.fr = 0 → σ.sg = 0 → σ.dt = ∅ →
  HsEmpty hs →
  csm.Voters' = [] →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  σ.fl = W64 0 →
  sn.unrec = sn →
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  γ.reNoSnap = false →
  -- (step 5) in place of `TraceLoggerOk cv.TraceLogger'` (now in `trCapStart`) and `γ.reTrace = none`
  (γ.reTrace ≠ none → cv.PreVote' = false ∧ cv.CheckQuorum' = false ∧ ps.length < 2 ^ 40) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 1) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 0) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ ∗
              -- (step 5) the storage's no-compaction (traced: from the client's contract)
              trNoCut γ.reTrace (interface.ok si) ∗ R' }}) ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      bootInit γ md cv.ID' (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      certLink γ sn ∗
      -- (step 5) the capability's start (untraced: the nil logger)
      trCapStart γ.reTrace γ cv.ID' cv.TraceLogger' (bootCfg ps) (bootPhase ps cv.ID') bootNone }}
    (App (App (Val #(functions setupNode [])) (Val #c)) (Val #peers))
  {{ (n : Loc), RET #n;
      R' ∗ ∃ (nv : node) (rn : Loc),
        n ↦ nv ∗ ⌜nv.rn' = rn⌝ ∗ newNodeChans nv ∗
        ownRawNode γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 1,
            storage := interface.ok si, sn := sn, mode := md,
            cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 } ∗
        peers ↦*{dq} pv ∗
        -- (step 5, A8.3) the completion witness
        bootDoneG γ.reTrace cv.ID' }}

end spec

end EtcdGrove
end Perennial
