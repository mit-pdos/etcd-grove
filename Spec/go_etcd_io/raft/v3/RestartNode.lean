/- Lean-first (no Rocq counterpart).

## `RestartNode(c)` (node.go:281)

`NewRawNode(c)` (its premises: a node of a new cluster, `Spec/NewRawNode.lean`) in a
`node` whose goroutine `run` it starts, for the cluster's term budget `bud`
(`budget_alloc`, `InvNode.lean`). It returns the node (`isNode`, persistent: what
`Propose`, `Step`, `Tick` and `Ready` take) and the driver's token (`nodeDriver`, at
the empty committed log: what `node_ready_receive` and `Advance` take). Since 2026-10-10
also the cluster's proposed slices (`propDataInv`, allocated once with the raft ghost
state), which `isNode` keeps with the commit invariant. Since 2026-10-15 (stage N) in either
mode (`md`, `NewRawNode`'s `rnInit`: statically `ownRaftGhost` at the initial state, dynamically
B5's `ownRaftGhostR` at `rinit c0`), and with the driver's view of the configuration
(`nodeCfg`, at index `0` and the initial configuration) for `ApplyConfChange` and `Advance`.

raft v3.7 (2026-10-16, stage R5): `NewRawNode`'s premises as they are now (the storage's
`InitialState` in `newRaft`'s D7 shape, the conf state's record `csm`); **no proposed slices'
invariant** (D6: an entry's data is its bytes; until then `inv propDataN (propDataInv γ)`, which
`isNode` kept).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Spec.go_etcd_io.raft.v3.NewRawNode

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
abbrev RestartNode.spec : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM),
  -- `NewRawNode`'s premises
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.CheckQuorum' = false →
  cv.DisableProposalForwarding' = false →
  -- `ReadOnlySafe` (2026-10-12)
  cv.ReadOnlyOption' = W64 0 →
  -- conf-change validation on (2026-10-13; `newRaft`'s premise)
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.PreVote' = false →
  cv.Applied' = W64 0 →
  σ.prev = entryID.mk (W64 0) (W64 0) →
  σ.ents = [] →
  (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] →
  HsEmpty hs →
  -- (2026-10-16, stage R5) the conf state's record `csm`, as `NewRawNode`'s
  csm.Voters' ≠ [] → csm.Voters'.Nodup → W64 0 ∉ csm.Voters' →
  (csm.Voters'.length : Int) ≤ 2 ^ 62 →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  γ.reCfg = GMap.listToSet csm.Voters' →
  cv.ID' ∈ csm.Voters' →
  -- (2026-10-15, stage N) the dynamic mode with `StepDownOnRemoval` (`NewRawNode`'s)
  (md.isDyn = true → cv.StepDownOnRemoval' = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      -- (2026-10-16, stage R5) `NewRawNode`'s (`newRaft`'s, stage R4, D7)
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc), ownStorage (interface.ok si) { σ with ss := ss' } -∗ hsOpt hp hs -∗
            csPts cs DFrac.discard csm true -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      -- (2026-10-15, stage N) the ghost state in the mode `md` (`NewRawNode`'s `rnInit`; until
      -- then `ownRaftGhost γ cv.ID' initPState`, the static mode's)
      rnInit γ md cv.ID' (GMap.listToSet csm.Voters') ∗ isCommitted γ [] ∗
      -- the cluster's term budget
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 0) }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = md ∧
         nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode γn cv.ID' n ∗ nodeDriver γn cv.ID' n [] ∗
        -- (2026-10-15, stage N) the driver's view of the configuration: the initial one
        nodeCfg γn 0 (cfgState (GMap.listToSet csm.Voters') ∅) }}

end spec

end EtcdGrove
end Perennial
