/-
Lean-first (no Rocq counterpart).

# Starting a replica's node (2026-11-01, durability stage II (l))

What `StartCluster` (each founder) and `Cluster.startNew` (a newcomer) share at their
`RestartNode` call, on a fresh storage (the empty contents `kvrBootContents`):

- the storage holds a node that has stored nothing (`kvrBoot_holds`);
- the update `RestartNode` takes fires at once over the allocation's `raftState` at
  `RaftState.init`, and gives it back with the state it read (`kvr_restartAu`);
- the driver `RestartNode` returns from the empty contents is `NodeDriverState.init`
  (`kvr_startDriver`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section start
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- The fresh storage's contents: the zero hard state, no snapshot, the base `⟨0, 0⟩`, no
entries. -/
abbrev kvrBootContents : StorContents :=
  ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩

theorem kvrBoot_holds : StorageHolds RaftState.init kvrBootContents := by
  unfold StorageHolds
  refine ⟨Int.le_refl _, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [plogTermAt, RaftState.init]
  · rfl
  · simp [StorContents.b, StorContents.commit]
  · simp [StorContents.commit, RaftState.init]
  · intro sv h; cases h
  · intro h; exact absurd rfl h

theorem kvr_startDriver (si : Storage) (l : List LogEntry) (K : GName) (S : RaftState)
    (hl : l = []) (hS : S = RaftState.init) :
    (⟨si, l, kvrBootContents.hs, none, K, S, StateFollower⟩ : NodeDriverState) =
      NodeDriverState.init si K := by
  subst hl hS; rfl

variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **The update `RestartNode` takes, fired at once**: over the node's durable state at
`RaftState.init` (allocation's), which the storage `σ` holds; it gives the state back, with the
fact that it is `RaftState.init`. -/
theorem kvr_restartAu (γ : Cluster) (N : Namespace) (id : w64) (σ : StorContents)
    (Hσ : StorageHolds RaftState.init σ) :
    raftState (GF := GF) γ id RaftState.init ⊢
      AU <{ ∃∃ (S : RaftState), raftState γ id S ∗ ⌜StorageHolds S σ⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ id S,
            COMM (fun S => iprop(raftState γ id S ∗ ⌜S = RaftState.init⌝)) S }> := by
  iintro H
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑N from Std.LawfulSet.empty_subset)
  iintro Hclose
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists RaftState.init
  iframe H
  isplitr
  · ipureintro; exact Hσ
  isplit
  · iintro ⟨H, -⟩
    imod Hclose with -
    imodintro
    iexact H
  · iintro H
    imod Hclose with -
    imodintro
    iframe H
    ipureintro; rfl

end start

end kvreconf
end EtcdGrove
end Perennial
