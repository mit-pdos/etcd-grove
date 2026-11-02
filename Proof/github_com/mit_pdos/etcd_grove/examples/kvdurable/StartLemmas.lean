/-
Lean-first (no Rocq counterpart).

# Starting an incarnation: what `Cluster.start` needs besides its callees (2026-11-01)

- **The update `RestartNode` takes** (`kd_restartAu`): over the durable state `S` in the file's
  invariant (`kdFileInv`), opened inside it (`RestartNode`'s update reads `▷ raftState`, so no later
  is to be taken off), at the state `S` the writer's half pins (kvreconf's `kvr_restartAu`, at the
  durable state `S` the storage holds); it gives back the writer's half, with the fact that it is `S`.
- **The frozen prefix cut** (`memLog_take_le`): `openStorage`'s frozen entries, up to the snapshot's
  index, cut at the delivered log's length (`newReplica`'s frozen record).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Spec.go_etcd_io.raft.v3.RestartNode

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

namespace kvdurable

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- The file's contents, or the empty storage's image if there is no file. -/
def kdImgOf (o : Option StorFile) : StorFile := o.getD imgEmpty

/-- **The update `RestartNode` takes** (kvreconf's `kvr_restartAu`): over the durable state in the
file's invariant, opened inside the update (it reads `▷ raftState`); the writer's half pins it at
`S`, which the storage `σ` holds. It gives the writer's half back, with the fact that the state is
`S`. -/
theorem kd_restartAu (γ : KdNames) (dir : GoString) (id : w64) (σ : StorContents) (S : RaftState)
    (o : Option StorFile) (Hσ : StorageHolds S σ) :
    kdFileInv (GF := GF) γ dir id ∗ kdWriter γ id S o ⊢
      AU <{ ∃∃ (S' : RaftState), ▷ raftState γ.r.cluster id S' ∗ ⌜StorageHolds S' σ⌝ }>
         @ ⊤ \ ↑kdRaftN, ∅
         <{ raftState γ.r.cluster id S',
            COMM (fun S' => iprop(kdWriter γ id S o ∗ ⌜S' = S⌝)) S' }> := by
  have : Inhabited RaftState := ⟨RaftState.init⟩
  iintro ⟨#Hinv, Hwr⟩
  iauintro
  unfold atomic_acc
  iunfold kdFileInv at Hinv
  iinv Hinv with HI Hclose
  · exact kdRepN_raft id
  icases HI with ⟨%S0, %o0, ⟨HrS, Hdf⟩, >Hwv, >%HSH, HcF⟩
  iunfold kdWriter at Hwr
  ihave %Hag := ghostVar_agree (γ.wr id) _ _ _ _ $$ Hwr Hwv
  obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
  subst h1
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kdRaftN) \ ↑(kdRepN .@ uint.nat id) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists S
  iframe HrS
  isplitr
  · ipureintro; exact Hσ
  isplit
  · iintro ⟨HrS, -⟩
    imod Hclose2 with -
    imod Hclose $$ [HrS Hdf Hwv HcF] with -
    · inext
      iexists S, o0
      iframe HrS Hdf Hwv HcF
      ipureintro; exact HSH
    imodintro
    unfold kdWriter
    iexact Hwr
  · iintro HrS
    imod Hclose2 with -
    imod Hclose $$ [HrS Hdf Hwv HcF] with -
    · inext
      iexists S, o0
      iframe HrS Hdf Hwv HcF
      ipureintro; exact HSH
    imodintro
    unfold kdWriter
    iframe Hwr
    ipureintro; rfl

/-- No file holds what a node at the initial state holds. -/
theorem kdEmpty_holds : StorageHolds RaftState.init (kdContents none) := by
  unfold StorageHolds
  refine ⟨Int.le_refl _, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [plogTermAt, RaftState.init, kdContents, kdEmpty]
  · rfl
  · simp [StorContents.b, StorContents.commit, kdContents, kdEmpty]
  · simp [StorContents.commit, RaftState.init, kdContents, kdEmpty]
  · intro sv h; simp [kdContents, kdEmpty] at h
  · intro h; exact absurd rfl h

/-- **A replica's file, before its first start** (`StartCluster`, `startNew`): from the file's entry
(no file), the writer's variable whole and the id's durable state at `RaftState.init`, its invariant
at no contents and the writer's half. -/
theorem kdFile_alloc (γ : KdNames) (dir : GoString) (id : w64) (E : CoPset)
    (g : RaftState × Option GoString) :
    ⊢ dfile (GF := GF) γ.files (kdFileName dir id) none -∗ ghostVar (γ.wr id) (1 : Qp) g -∗
      raftState γ.r.cluster id RaftState.init ={E}=∗
      kdFileInv γ dir id ∗ kdWriter γ id RaftState.init none := by
  iintro Hdf Hg HrS
  imod ghostVar_update (RaftState.init, kdFileVal (none : Option StorFile)) (γ.wr id) g $$ Hg with Hg
  icases (ghostVar_split_half (GF := GF) (γ.wr id) (1 : Qp) _).1 $$ Hg with ⟨Hw1, Hw2⟩
  ihave Hinv : iprop(|={E}=> kdFileInv γ dir id) $$ [HrS Hdf Hw1]
  · unfold kdFileInv
    iapply inv_alloc
    inext
    iexists RaftState.init, none
    isplitl [HrS Hdf]
    · iframe HrS; iExactEq Hdf; rfl
    iframe Hw1
    isplitl []
    · ipureintro; exact ⟨kdEmpty_holds, fun f h => by cases h⟩
    iintro %f %h; cases h
  imod Hinv with #Hinv
  imodintro
  iframe Hinv
  unfold kdWriter
  iexact Hw2

/-- **A frozen prefix cut shorter**: the entries of `xs.take n` from `k` frozen give those of
`xs.take m`, for `m ≤ n`. -/
theorem memLog_take_le (γs : MemStorNames) (k : Nat) (xs : List EntryM) (m n : Nat) (h : m ≤ n) :
    memLog (GF := GF) γs k DFrac.discard (xs.take n) ⊢ memLog γs k DFrac.discard (xs.take m) := by
  have e : xs.take n = xs.take m ++ (xs.take n).drop m := by
    conv => lhs; rw [← List.take_append_drop m (xs.take n)]
    rw [List.take_take, Nat.min_eq_left h]
  rw [e]
  iintro H
  icases (memLog_app γs k DFrac.discard _ _).1 $$ H with ⟨H, -⟩
  iexact H

end start

end kvdurable
end EtcdGrove
end Perennial
