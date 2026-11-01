/-
Lean-first (no Rocq counterpart).

# Starting an incarnation: what `Cluster.start` needs besides its callees (2026-11-01)

- **Borrowing the file's durable state** (`kdFile_lend`, `kdFile_return`): `RestartNode`'s update
  reads `raftState` inside `RestartNode`, with no step to take the file invariant's later off
  (`raftState` is not timeless), so `Cluster.start` takes the durable state and the file's entry out
  of `kdFileInv` beforehand (leaving its writer's half in their place: the lent case) and puts them
  back after `RestartNode`, each time with a later credit.
- **The update `RestartNode` takes** (`kd_restartAu`): over the borrowed `raftState`, fired at once
  (kvreconf's `kvr_restartAu`, at the durable state `S` the storage holds), giving it back with the
  fact that it is `S`.
- **The frozen prefix cut** (`memLog_take_le`): `openStorage`'s frozen entries, up to the snapshot's
  index, cut at the delivered log's length (`newReplica`'s frozen record).
- **S1b** (`restart_delivered_stored_S1b`, a `sorry` until raft adds it to `RestartNode`'s post):
  the restarted node's delivered log `l` agrees with the stored entries above the log's start
  (`(LogEntry.toEntries l 0).drop σ.b = σ.ents.take (l.length - σ.b)`), as a strengthening of
  `RestartNode.spec` (`RestartNodeS1b.spec`).
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

section s1b
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `RestartNode.spec` with S1b in its post: the delivered log `l` agrees with the stored entries
above the log's start (what raft is adding to `RestartNode`'s post). -/
abbrev RestartNodeS1b.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorContents) (csm : ConfStateM) (a : Nat) (m : Membership)
    (Q : RaftState → IProp GF) (F : GName → IProp GF),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  (uint.nat cv.Applied' = 0 ∨ σ.b ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ σ.commit) →
  max σ.b (uint.nat cv.Applied') ≤ a → a ≤ σ.commit →
  γ.bootLen ≤ σ.commit →
  confStateIs csm m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacant γ cv.ID' ∗
      AU <{ ∃∃ (S : RaftState), raftState γ cv.ID' S ∗ ⌜StorageHolds S σ⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ cv.ID' S, COMM Q S }> ∗
      confAt γ a m ∗
      restartStorage γ (interface.ok si) σ csm (uint.nat cv.Applied') F }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (S : RaftState) (l : List LogEntry) (K : GName),
        ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗
        isCommittedLogLb γ l ∗ ⌜l.length = max σ.b (uint.nat cv.Applied')⌝ ∗
        -- S1b
        ⌜(LogEntry.toEntries l 0).drop σ.b = σ.ents.take (l.length - σ.b)⌝ ∗
        nodeDriver n γ N ⟨interface.ok si, l, σ.hs, none, K, S, StateFollower⟩ ∗
        nodeConfig n γ N ⟨a, m⟩ ∗
        nodeRunning n γ N 1 ∗
        Q S ∗ F K }}

/-- **S1b** (2026-11-01; `sorry` until raft's `RestartNode` post gives it, then this lemma goes): the
restarted node's delivered log is the stored log above its start. -/
theorem restart_delivered_stored_S1b (wp : RestartNode.spec (GF := GF) (hG := hG)) :
    RestartNodeS1b.spec (GF := GF) (hG := hG) := by
  sorry

end s1b

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

/-- **Borrow the file's durable state** (see the file header): the writer's half, which pins it
at `(S, kdFileVal o)`, goes into the invariant (its lent case); out come the durable state, the
file's entry, the contents' facts and the stored snapshot's certificate (of the contents `o'` the
invariant names: their bytes are `o`'s). -/
theorem kdFile_lend (γ : KdNames) (dir : GoString) (id : w64) (S : RaftState) (o : Option StorFile)
    (E : CoPset) (HE : ↑(kdRepN .@ uint.nat id) ⊆ E) :
    ⊢ kdFileInv (GF := GF) γ dir id -∗ kdWriter γ id S o -∗ £ 1 ={E}=∗
      ∃ o' : Option StorFile, ⌜kdFileVal o' = kdFileVal o⌝ ∗ raftState γ.r.cluster id S ∗
        dfile γ.files (kdFileName dir id) (kdFileVal o') ∗
        ⌜StorageHolds S (kdContents o') ∧ ∀ f, o' = some f → KdFileOk f⌝ ∗
        kdSnapCert γ (kdImgOf o').snap := by
  iintro #Hinv Hwr Hlc
  iunfold kdFileInv at Hinv
  iinv Hinv with HI Hclose
  imod lc_fupd_elim_later $$ Hlc HI with HI
  icases HI with ⟨%S0, %o0, HD, Hwv, %HSH, HcF⟩
  icases HD with (⟨HrS, Hdf⟩ | Hlent)
  rotate_left
  · iexfalso
    iapply kdWriter_lent_absurd γ id _ _ _ _
    iframe Hwr Hwv Hlent
  iunfold kdWriter at Hwr
  ihave %Hag := ghostVar_agree (γ.wr id) _ _ _ _ $$ Hwr Hwv
  obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
  subst h1
  ihave #Hcert : kdSnapCert γ (kdImgOf o0).snap $$ [HcF]
  · cases o0 with
    | none =>
      unfold kdImgOf kdSnapCert
      ileft; ipureintro; rfl
    | some f =>
      unfold kdImgOf
      simp only [Option.getD_some]
      iapply HcF $$ %f %rfl
  imod Hclose $$ [Hwv Hwr HcF] with -
  · inext
    iexists S, o0
    isplitl [Hwr]
    · iright; rw [← h2]; iexact Hwr
    iframe Hwv HcF
    ipureintro; exact HSH
  imodintro
  iexists o0
  iframe HrS Hdf Hcert
  ipureintro; exact ⟨h2.symm, HSH⟩

/-- **Give the borrowed durable state back** (see the file header): the durable state and the
file's entry go back into the invariant, whose lent case held the writer's half, which comes out. -/
theorem kdFile_return (γ : KdNames) (dir : GoString) (id : w64) (S : RaftState) (o : Option StorFile)
    (E : CoPset) (HE : ↑(kdRepN .@ uint.nat id) ⊆ E)
    (HSH : StorageHolds S (kdContents o)) (Hok : ∀ f, o = some f → KdFileOk f) :
    ⊢ kdFileInv (GF := GF) γ dir id -∗ raftState γ.r.cluster id S -∗
      dfile γ.files (kdFileName dir id) (kdFileVal o) -∗ kdSnapCert γ (kdImgOf o).snap -∗ £ 1 ={E}=∗
      kdWriter γ id S o := by
  iintro #Hinv HrS Hdf #Hcert Hlc
  iunfold kdFileInv at Hinv
  iinv Hinv with HI Hclose
  imod lc_fupd_elim_later $$ Hlc HI with HI
  icases HI with ⟨%S0, %o0, HD, Hwv, %HSH0, HcF⟩
  icases HD with (⟨HrS0, Hdf0⟩ | Hlent)
  · iexfalso
    iapply dfile_excl $$ Hdf Hdf0
  imod ghostVar_update_halves (S, kdFileVal o) (γ.wr id) _ _ $$ Hwv Hlent with ⟨Hwv, Hwr⟩
  imod Hclose $$ [HrS Hdf Hwv] with -
  · inext
    iexists S, o
    isplitl [HrS Hdf]
    · ileft; iframe HrS Hdf
    iframe Hwv
    isplitl []
    · ipureintro; exact ⟨HSH, Hok⟩
    iintro %f %hf
    subst hf
    iExactEq Hcert; rfl
  imodintro
  unfold kdWriter
  iexact Hwr

/-- **The update `RestartNode` takes, fired at once** (kvreconf's `kvr_restartAu`): over the
borrowed durable state `S`, which the storage `σ` holds; it gives the state back, with the fact that
it is `S`. -/
theorem kd_restartAu (γ : Cluster) (N : Namespace) (id : w64) (σ : StorContents) (S : RaftState)
    (Hσ : StorageHolds S σ) :
    raftState (GF := GF) γ id S ⊢
      AU <{ ∃∃ (S' : RaftState), raftState γ id S' ∗ ⌜StorageHolds S' σ⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ id S',
            COMM (fun S' => iprop(raftState γ id S' ∗ ⌜S' = S⌝)) S' }> := by
  iintro H
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑N from Std.LawfulSet.empty_subset)
  iintro Hclose
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists S
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
