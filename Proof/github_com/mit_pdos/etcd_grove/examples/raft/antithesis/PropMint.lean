/-
Lean-first (no Rocq counterpart). #33 S4, `RunCluster`'s proposer (`notes/antithesis-s4-design.md`
§9): **a proposal's raft resources** (`propOk γ data`, what `Cluster.deliver` hands the node with an
`inProp` input and `RawNode.Propose` takes), minted for any data.

Raft's proposals carry a ticket (`entTk`) and their data's certificate (`propData`), which raft's
ghost state mints from the client's atomic update of the committed client log
(`ownCommittedOps`): raft fires it when it appends the proposal's entry (`node.Propose`'s premise).
The harness does not track the client log, so it keeps the log's authority in an invariant of its
own (`opsInv`, namespace `antOpsN`, outside raft's `N`), from which every proposal's update is built
(`ops_au`): the log grows by the entry, nothing else.

The minting itself is raft's (`propMint.law`): proved by raft's internals (`api_key_register`,
`api_propAu1_if`, `prop_deposit`; `node__Propose.lean`'s ghost steps), which the node API seals; it
is a hypothesis here until raft's RawNode API exports it (requested of raft, 2026-11-24: the same
statement, with that proof). `RunCluster`'s proof takes it as a law callee.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv
public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The harness's client-log invariant's namespace. -/
def antOpsN : Namespace := nroot.@"antithesis_ops"

section mint
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **Raft's minting of a proposal's resources** (a law of raft's RawNode API, requested): for the
client's update of the committed client log by the proposal's entry, the entry's data certificate
and ticket. -/
abbrev propMint.law : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (data : List w8) (E : CoPset), ↑N ⊆ E →
    ⊢ isCluster (GF := GF) γ N -∗
      □?γ.dup (AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64), ownCommittedOps γ (ops ++ [⟨t, W32 0, data⟩]), COMM True }>) ={E}=∗
      propData γ.raftNames (propEntryM data) ∗ entTk γ.raftNames (propEntryM data)

/-- **The harness's client log** (an invariant): the committed client log's authority, at whatever
it is; the harness reads nothing of it. -/
def opsInv (γ : Cluster) : IProp GF :=
  inv antOpsN iprop(∃ ops : List LogEntry, ownCommittedOps γ ops)

instance opsInv_persistent (γ : Cluster) : Persistent (opsInv (GF := GF) γ) := by
  unfold opsInv; infer_instance

/-- Allocating `opsInv` from the log's authority (`RunCluster`, after raft's allocation). -/
theorem opsInv_alloc (γ : Cluster) (ops : List LogEntry) (E : CoPset) :
    ⊢ ownCommittedOps (GF := GF) γ ops ={E}=∗ opsInv γ := by
  iintro Hops
  unfold opsInv
  iapply inv_alloc antOpsN E
  inext
  iexists ops
  iexact Hops

/-- **A proposal's update, from `opsInv`**: the log grows by the entry. -/
theorem ops_au (γ : Cluster) (N : Namespace) (data : List w8)
    (Hdisj : (↑antOpsN : CoPset) ⊆ ⊤ \ ↑N) :
    ⊢ opsInv (GF := GF) γ -∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64), ownCommittedOps γ (ops ++ [⟨t, W32 0, data⟩]), COMM True }> := by
  iintro #Hinv
  iauintro
  unfold atomic_acc opsInv
  iinv Hinv with ⟨%ops, >Hops⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑N) \ ↑antOpsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops] with -
    · inext
      iexists ops
      iexact Hops
    imodintro
    iempintro
  · iintro %t Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops] with -
    · inext
      iexists ops ++ [⟨t, W32 0, data⟩]
      iexact Hops
    imodintro
    iempintro

/-- **A proposal's raft resources, minted** (`propOk`): through raft's law, at the update built from
`opsInv`, in a cluster of single updates (`dup` off) with no bound on proposed data. -/
theorem propOk_mint (Hlaw : propMint.law (GF := GF)) (γ : AntNames) (N : Namespace)
    (data : List w8) (E : CoPset) (HN : ↑N ⊆ E) (Hdisj : (↑antOpsN : CoPset) ⊆ ⊤ \ ↑N)
    (Hdup : γ.raft.dup = false) (Hmd : γ.raft.raftNames.maxData = none) :
    ⊢ isCluster (GF := GF) γ.raft N -∗ opsInv γ.raft ={E}=∗ propOk γ data := by
  iintro #Hcl #Hops
  ihave Hau := ops_au γ.raft N data Hdisj $$ Hops
  have Hl := Hlaw γ.raft N data E HN
  rw [Hdup] at Hl
  imod Hl $$ Hcl Hau with ⟨#Hd, Htk⟩
  imodintro
  unfold propOk
  iframe Hd Htk
  ipureintro
  intro b hb
  rw [Hmd] at hb
  cases hb

end mint

end AntHarness
end EtcdGrove
end Perennial
