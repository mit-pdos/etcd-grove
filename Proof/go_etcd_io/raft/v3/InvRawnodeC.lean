/-
A `RawNode` detached from the protocol, at any configuration (2026-10-13, reconfiguration
stage A2), Lean-first.

`ownRawNode γ rn id rs` (`InvRawnode.lean`) ties the node to the ghost state `γ`, whose voter
set (`γ.reCfg`) is fixed: the protocol is proved at a fixed configuration only. After an
`ApplyConfChange` that changes the configuration (or adds learners), the node leaves that
world: `ownRawNodeC c rn id s` is the node's memory only -- the `RawNode` struct, the raft
struct at the configuration `c` (`ownRaftPhysC`, physical state `s`), the queue `Advance` will
step -- with no `γ`, no ghost state, no promise about committed entries or the client log
(`isCommitted`, `RNState`). Nothing here says the configuration is `γ.reCfg`, or anything about
`γ` at all.

The order of `ApplyConfChange` and `Advance` (`issues/raft-advance-before-applyconfchange.md`)
is not a premise here: `s` records the applied index and the log, `c` the configuration in use,
but not which conf-change entries `c` reflects -- that would need the decoded entries' history
(their bytes are heap, `Unmarshal`ed by the leader only), which the physical state does not
keep. It is stated in the documentation of `RawNode.ApplyConfChange.spec`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.InvApplyConfC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section rawnodeC
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `RawNode` at the configuration `c`, physical state `s`, detached from the protocol (see
the file header): `ownRawNode`'s memory without its ghost state. -/
def ownRawNodeC (c : CfgM) (rn : Loc) (id : w64) (s : NState) : IProp GF :=
  iprop(∃ (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message) (ps : List Pending),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysCV c c.voters rnv.raft' id s ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps;ps, pendingOwn m p))

theorem ownRawNodeC_intro (c : CfgM) (rn : Loc) (id : w64) (s : NState) (rnv : RawNode)
    (sv : SoftState) (steps : List raftpb.Message) (ps : List Pending)
    (Hasync : rnv.asyncStorageWrites' = false) :
    ⊢ rawNodeOwn (GF := GF) rn rnv -∗ ownRaftPhysCV c c.voters rnv.raft' id s -∗
      rnv.prevSoftSt' ↦□ sv -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) -∗
      ([∗list] _k ↦ m;p ∈ steps;ps, pendingOwn m p) -∗
      ownRawNodeC c rn id s := by
  iintro Hrn Hphys #Hsoft Hsteps Hcap Hpown
  unfold ownRawNodeC
  iexists rnv, sv, steps, ps
  simp only [named]
  iframe Hrn Hphys Hsoft Hsteps Hcap Hpown
  ipureintro; exact Hasync

end rawnodeC

/-! ## The scope of a configuration-changing `ApplyConfChange` -/

section model
variable [FfiSyntax]

/-- A change that `applyConfChange` carries out (no `confchange` error, no undefined
transition: `ccApplyM` answers) at a node with the voters `cfg` and any learners `lrn`
it may track, keeping the node `id` a voter of either half of the result, and tracking at
most `2^62` ids afterwards (`ownTrackerC`'s bound; a client sees neither the learners nor
their number, so the bound is asked for every learner set that fits the old bound). -/
def CCApplies (cfg : GSet w64) (id : w64) (t : raftpb.ConfChangeTransition)
    (ccs : List raftpb.ConfChangeSingle) : Prop :=
  ∀ lrn : GSet w64, (∀ k, k ∈ lrn → k ∉ cfg) → (GMap.size (cfg ∪ lrn) : Int) ≤ 2 ^ 62 →
    ∃ c' : CCState, ccApplyM t ccs (cfgState cfg lrn) = some c' ∧
      (GMap.size c'.cfg.ids : Int) ≤ 2 ^ 62 ∧ id ∈ c'.cfg.voters

/-- A shrinking change (stage L's scope) applies, at a voter. -/
theorem CCShrink.applies {cfg : GSet w64} {id : w64} {t : raftpb.ConfChangeTransition}
    {ccs : List raftpb.ConfChangeSingle} (H : CCShrink cfg t ccs) (Hin : id ∈ cfg) :
    CCApplies cfg id t ccs := by
  intro lrn Hd Hsz
  obtain ⟨lrn', Hl, Hm⟩ := H lrn Hd
  refine ⟨_, Hm, ?_, ?_⟩
  · have h1 : (cfgState cfg lrn').cfg.ids ⊆ cfg ∪ lrn := by
      show (CfgM.simple cfg lrn').ids ⊆ _
      unfold CfgM.ids; rw [CfgM.voters_simple]
      rw [GMap.elem_of_subseteq]; intro k hk
      rcases (GMap.elem_of_union _ _ _).1 hk with h | h
      · exact GMap.elem_of_union_l _ h
      · exact GMap.elem_of_union_r _ ((GMap.elem_of_subseteq _ _).1 Hl k h)
    have h2 := GMap.subseteq_size h1
    omega
  · show id ∈ (CfgM.simple cfg lrn').voters
    rw [CfgM.voters_simple]; exact Hin

end model

end EtcdGrove
end Perennial
