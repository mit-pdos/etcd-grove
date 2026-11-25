/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/RunCluster.lean` (the trace check's
`RunConcurrent.lean` is the template; the ghost start is `RunClusterAlloc.lean`'s).

The setup (the stop channel, the recorder, the storage registry, raft's cluster `cluster_alloc_names`
through `clusterAllocFacts.law`), the voters, the three nodes made (`nodeMade`), the run's names and
invariant (`antInv_alloc`); the boot loop (per node its `boot` report and drain, on the caller's
thread token); the `go c.run(n)` loop (`nodesWg.Add(1)` with the node's `nodeExit`, the goroutine
forked with a fresh token, `wp_fork_tok_body`, which `Cluster.run` gives back; the network's adders
split a half and two quarters, `antQ`); the proposer (`joinN` at `1`), which loops until it sees the
stop channel closed (a non-blocking receive) and mints each proposal's raft resources
(`propOk_mint`); then the stop: the stop channel closed, the proposer waited for, `nodesWg.Wait()` (the three `nodeExit`s back), the network's adders joined
and closed (`njClose`) and `netWg.Wait()`, and the run's invariant closed (`antInv_close`): `runOver`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__drain
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.names
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunClusterAlloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSendWp
public import Proof.go_etcd_io.raft.v3.RawNodeApi
public import Perennial.Spec.strconv.FormatUint
public import Perennial.Spec.time.Sleep
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

set_option hygiene false in
/-- Step to the next `GoOp` in evaluation position and take it, with its time receipt `H`. -/
macro "wp_take_op_receipt" " as " H:ident : tactic => `(tactic| (
  repeat (
    fail_if_success wp_bind (App (Val (GoInstruction (GoOp _ _))) (Val _))
    first | wp_pure | wp_load | wp_store | wp_alloc_auto)
  wp_bind (App (Val (GoInstruction (GoOp _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => first | exact isPanic_intoVal _ | rfl
  inext
  iintro $H:ident -
  iapply wp_value'))

/-! The range loops over the nodes are proved by `wp_slice_for_range_drain`. -/
attribute [-instance] pure_wp_slice_for_range

/-- The configuration `RunCluster` starts node `id` with, on the wrapper `s`. -/
abbrev antConfig [GooseExts] [GoGlobalContext] (id : w64) (s : Loc) : Config :=
  { ID' := id, ElectionTick' := W64 10, HeartbeatTick' := W64 1,
    Storage' := interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty) #s,
    Applied' := 0, AsyncStorageWrites' := false, MaxSizePerMsg' := W64 1048576,
    MaxCommittedSizePerReady' := 0, MaxUncommittedEntriesSize' := 0, MaxInflightMsgs' := W64 256,
    MaxInflightBytes' := 0, CheckQuorum' := false, PreVote' := false, ReadOnlyOption' := 0,
    Logger' := interface.mkOk github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger.ty
      #(zero_val github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger),
    DisableProposalForwarding' := false, DisableConfChangeValidation' := false,
    StepDownOnRemoval' := false, TraceLogger' := interface.nil }

theorem antConfig_valid [GooseExts] [GoGlobalContext] (id : w64) (s : Loc)
    (h1 : 1 ≤ uint.Z id) (h2 : uint.Z id ≤ 3) : ConfigValid (antConfig id s) := by
  unfold ConfigValid
  refine ⟨?_, ?_, ?_, ⟨by show (0 : Int) < sint.Z (W64 1); decide,
    by show sint.Z (W64 1) < sint.Z (W64 10); decide⟩, by simp, by show (0 : Int) < sint.Z (W64 256); decide,
    Or.inl rfl, by simp, Or.inl rfl⟩ <;> (intro h; subst h; revert h1 h2; decide)

section logger
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- The harness's `quietLogger{}` meets raft's `Logger` contract: its formatting methods return. -/
theorem antLogger_isLogger :
    ⊢ isLogger (GF := GF) ⟨github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger.ty,
        #(zero_val github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger)⟩ := by
  unfold isLogger
  iintro %meth %Hmeth %format %args
  simp only [logMethods, List.mem_cons, List.not_mem_nil, or_false] at Hmeth
  rcases Hmeth with rfl | rfl | rfl | rfl <;>
  · dsimp only
    imodintro
    iintro %Φ - HΦ
    wp_method_call
    wp_auto
    iapply HΦ
    itrivial

end logger

/-- Node `j`'s index in `Fin 3`. -/
def finOf (j : Nat) : Fin 3 := ⟨j % 3, Nat.mod_lt _ (by decide)⟩

theorem finOf_id (j : Nat) (h : j < 3) : AntSim.nodeId (finOf j) = W64 ((j : Int) + 1) := by
  unfold AntSim.nodeId finOf; simp [Nat.mod_eq_of_lt h]

theorem rc_step [GooseExts] (k : w64) (h1 : 1 ≤ uint.Z k) (h2 : uint.Z k ≤ 3) :
    [W64 1, W64 2, W64 3].drop (uint.nat k - 1) = k :: [W64 1, W64 2, W64 3].drop (uint.nat k) ∧
      uint.nat (k + W64 1) - 1 = uint.nat k ∧ 1 ≤ uint.Z (k + W64 1) ∧ uint.Z (k + W64 1) ≤ 4 ∧
      AntSim.nodeId (finOf (uint.nat k - 1)) = k ∧ uint.nat k - 1 + 1 = uint.nat k ∧
      k ∈ [W64 1, W64 2, W64 3] ∧ uint.nat k - 1 < 3 := by
  have : k = W64 1 ∨ k = W64 2 ∨ k = W64 3 := by
    have : uint.Z k = 1 ∨ uint.Z k = 2 ∨ uint.Z k = 3 := by omega
    rcases this with h | h | h
    · left; word
    · right; left; word
    · right; right; word
  rcases this with rfl | rfl | rfl <;> refine ⟨rfl, rfl, by decide, by decide, rfl, rfl, by decide, by decide⟩

theorem raftNs_mask : (↑((nroot.@"raft").@"raft") : CoPset) ⊆ ⊤ \ ↑antN := by
  intro x hx
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  unfold antN at h'
  exact ndot_ne_disjoint nroot (show "raft" ≠ "antithesis" by decide) x
    ⟨nclose_subseteq _ _ x hx, h'⟩

theorem rc_end [GooseExts] (k : w64) (h1 : uint.Z k ≤ 4) (h2 : ¬ uint.Z k ≤ 3) :
    uint.nat k - 1 = 3 := by word

theorem ant_pick [GooseExts] (b len : w64) (hb : uint.Z b < uint.Z (W64 3))
    (hl : 3 = sint.nat len) (h0 : 0 ≤ sint.Z len) :
    0 ≤ sint.Z b ∧ sint.Z b < sint.Z len ∧ (sint.Z b).toNat = uint.nat b ∧ uint.nat b < 3 :=
  ⟨by word, by word, by word, by word⟩

theorem opsNs_mask : (↑antOpsN : CoPset) ⊆ ⊤ \ ↑(nroot.@"raft") := by
  intro x hx
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  unfold antOpsN at hx
  exact ndot_ne_disjoint nroot (show "antithesis_ops" ≠ "raft" by decide) x ⟨hx, h'⟩

section chans
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A made node's input channel, before the run's names (its bag) exist. -/
def nodeChanOwn (n : Loc) (γch : ChanNames) : IProp GF :=
  iprop(∃ ch : Loc, n.[H.node, go!"in"] ↦□ ch ∗ isChan ch γch H.input ∗
    ownChan γch H.input (ChanState.Buffered []))

end chans

/-- The proposer's join's namespace. -/
def antPropN : Namespace := nroot.@"antithesis_proposer"

/-- Node `j`'s share of the network's adders: a half for node `0`, a quarter for the others. -/
def antQ (j : Nat) : Qp := if j = 0 then (1 : Qp).half else (1 : Qp).half.half

section tri
variable {GF : BundledGFunctors}

/-- Three nodes' states, the first `i` of them moved from `A` to `B`. -/
def tri (A B : Nat → IProp GF) (i : Nat) : IProp GF :=
  iprop((if 0 < i then B 0 else A 0) ∗ (if 1 < i then B 1 else A 1) ∗ (if 2 < i then B 2 else A 2))

theorem tri_split (A B : Nat → IProp GF) (i : Nat) (hi : i < 3) :
    tri A B i ⊢ A i ∗ (B i -∗ tri A B (i + 1)) := by
  unfold tri
  match i, hi with
  | 0, _ =>
    simp (config := { decide := true }) only [ite_true, ite_false]
    iintro ⟨H0, H1, H2⟩
    iframe H0
    iintro H0'
    iframe H0' H1 H2
  | 1, _ =>
    simp (config := { decide := true }) only [ite_true, ite_false]
    iintro ⟨H0, H1, H2⟩
    iframe H1
    iintro H1'
    iframe H0 H1' H2
  | 2, _ =>
    simp (config := { decide := true }) only [ite_true, ite_false]
    iintro ⟨H0, H1, H2⟩
    iframe H2
    iintro H2'
    iframe H0 H1 H2'

end tri

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- Node `j` before its boot drain: at its loop head, with the boot report's receipts. -/
def bootA (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) : IProp GF :=
  iprop(nodeOwn c γ j n antView0 (.loop [] pInit) ∗ ⧗ 3 ∗ nodeRO γ n j)

/-- Node `j` after its boot drain: between inputs. -/
def bootB (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) : IProp GF :=
  iprop(∃ v : AntSim.NodeView, nodeOwn c γ j n v .idle)

/-- The boot loop's state after `i` nodes. -/
def bootP (c : Loc) (γ : AntNames) (n0 n1 n2 : Loc) (i : Nat) : IProp GF :=
  iprop((if 0 < i then bootB c γ 0 n0 else bootA c γ 0 n0) ∗
    (if 1 < i then bootB c γ 1 n1 else bootA c γ 1 n1) ∗
    (if 2 < i then bootB c γ 2 n2 else bootA c γ 2 n2))

theorem bootP_split (c : Loc) (γ : AntNames) (n0 n1 n2 : Loc) (i : Nat) (hi : i < 3) :
    bootP (GF := GF) c γ n0 n1 n2 i ⊢
      bootA c γ (finOf i) ([n0, n1, n2][i]!) ∗
        (bootB c γ (finOf i) ([n0, n1, n2][i]!) -∗ bootP c γ n0 n1 n2 (i + 1)) := by
  unfold bootP
  match i, hi with
  | 0, _ =>
    simp (config := { decide := true }) only [ite_true, ite_false]
    iintro ⟨H0, H1, H2⟩
    isplitl [H0]
    · iExactEq H0; rfl
    iintro H0'
    iframe H1 H2
    iExactEq H0'; rfl
  | 1, _ =>
    simp (config := { decide := true }) only [ite_true, ite_false]
    iintro ⟨H0, H1, H2⟩
    isplitl [H1]
    · iExactEq H1; rfl
    iintro H1'
    iframe H0 H2
    iExactEq H1'; rfl
  | 2, _ =>
    simp (config := { decide := true }) only [ite_true, ite_false]
    iintro ⟨H0, H1, H2⟩
    isplitl [H2]
    · iExactEq H2; rfl
    iintro H2'
    iframe H0 H1
    iExactEq H2'; rfl

/-- A node's view and token, taken out and put back. -/
theorem nodeOwn_take (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView)
    (ph : Phase) :
    nodeOwn (GF := GF) c γ j n v ph ⊢ viewFrag γ j v ∗ nodeLive γ j ∗
      (viewFrag γ j v -∗ nodeLive γ j -∗ nodeOwn c γ j n v ph) := by
  unfold nodeOwn
  iintro ⟨%rn, %ms, %si, %rs, %ps, %qs, %ip, %cl, %applied, #Hrn, #Hms, Hbs, %Hsto, Hraw, Hnr,
    %Hrv, Hrole, Hterm, Hvote, Hcommit, Happ, Hcause, Hv, Hl, %HN, Hph⟩
  iframe Hv Hl
  iintro Hv Hl
  iexists rn, ms, si, rs, ps, qs, ip, cl, applied
  iframe Hrn Hms Hbs Hraw Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hph
  ipureintro; exact ⟨Hsto, Hrv, HN⟩

/-- Node `j`'s state before its `go c.run(n)`: between inputs, with its share of the network's
adders. -/
def goA (c : Loc) (γ : AntNames) (ns : List Loc) (j : Nat) : IProp GF :=
  iprop(bootB c γ (finOf j) ns[j]! ∗ netAdder c γ (antQ j) ∗ nodeRO γ ns[j]! (finOf j))

theorem bootP_three (c : Loc) (γ : AntNames) (n0 n1 n2 : Loc) :
    bootP (GF := GF) c γ n0 n1 n2 3 ⊢ bootB c γ 0 n0 ∗ bootB c γ 1 n1 ∗ bootB c γ 2 n2 := by
  unfold bootP
  simp (config := { decide := true }) only [ite_true]
  iintro H
  iexact H

theorem antQ_sum : antQ 0 + (antQ 1 + antQ 2) = 1 := by
  simp only [antQ, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, ite_false,
    ite_true]
  rw [Qp.half_add_half, Qp.half_add_half]

theorem go_start (c : Loc) (γ : AntNames) (n0 n1 n2 : Loc) :
    bootB (GF := GF) c γ 0 n0 ∗ bootB c γ 1 n1 ∗ bootB c γ 2 n2 ∗ netAdder c γ 1 ∗
      nodeRO γ n0 0 ∗ nodeRO γ n1 1 ∗ nodeRO γ n2 2 ⊢
      tri (goA c γ [n0, n1, n2]) (fun _ => iprop(True)) 0 := by
  rw [← antQ_sum]
  unfold tri goA netAdder
  simp (config := { decide := true }) only [ite_false]
  iintro ⟨B0, B1, B2, Had, #R0, #R1, #R2⟩
  icases njAdder_split _ _ _ _ _ $$ Had with ⟨A0, Had⟩
  icases njAdder_split _ _ _ _ _ $$ Had with ⟨A1, A2⟩
  isplitl [B0 A0]
  · isplitl [B0]
    · iExactEq B0; rfl
    iframe A0
    iExactEq R0; rfl
  isplitl [B1 A1]
  · isplitl [B1]
    · iExactEq B1; rfl
    iframe A1
    iExactEq R1; rfl
  isplitl [B2]
  · iExactEq B2; rfl
  iframe A2
  iExactEq R2; rfl

theorem go_end (c : Loc) (γ : AntNames) :
    tri (GF := GF) (fun _ => iprop(True)) (fun j => nodeExit c γ (finOf j) (antQ j)) 3 ⊢
      nodeLive γ 0 ∗ nodeLive γ 1 ∗ nodeLive γ 2 ∗ netAdder c γ 1 := by
  unfold tri nodeExit netAdder
  simp (config := { decide := true }) only [ite_true]
  iintro ⟨⟨L0, A0⟩, ⟨L1, A1⟩, ⟨L2, A2⟩⟩
  ihave A12 := njAdder_join _ _ _ _ _ $$ [A1 A2]
  · iframe A1 A2
  ihave A := njAdder_join _ _ _ _ _ $$ [A0 A12]
  · iframe A0 A12
  rw [antQ_sum]
  isplitl [L0]
  · iExactEq L0; rfl
  isplitl [L1]
  · iExactEq L1; rfl
  isplitl [L2]
  · iExactEq L2; rfl
  iexact A

theorem nodeRO_at (γ : AntNames) (n0 n1 n2 : Loc) (j : Nat) (hj : j < 3) :
    nodeRO (GF := GF) γ n0 0 ∗ nodeRO γ n1 1 ∗ nodeRO γ n2 2 ⊢
      nodeRO γ [n0, n1, n2][j]! (finOf j) := by
  match j, hj with
  | 0, _ =>
    iintro ⟨H, -, -⟩
    iExactEq H; rfl
  | 1, _ =>
    iintro ⟨-, H, -⟩
    iExactEq H; rfl
  | 2, _ =>
    iintro ⟨-, -, H⟩
    iExactEq H; rfl

theorem w32_step (i : Nat) (hi : i < 3) :
    sint.Z (W32 (i : Int)) < 2 ^ 31 - 1 ∧ W32 (i : Int) + W32 1 = W32 ((i + 1 : Nat) : Int) := by
  match i, hi with
  | 0, _ => exact ⟨by decide, by decide⟩
  | 1, _ => exact ⟨by decide, by decide⟩
  | 2, _ => exact ⟨by decide, by decide⟩

end boot

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem RunCluster.wp_proof
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : ∀ [AntStor GF], bootStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : ∀ [AntStor GF], bootStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : ∀ [AntStor GF], bootStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : ∀ [AntStor GF], bootStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : ∀ [AntStor GF], bootStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : ∀ [AntStor GF], bootStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_NewRawNode : ∀ [StorageModel GF], NewRawNode.emptyStartApiSpec (GF := GF) (hG := hG))
    (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_names : names.spec (GF := GF) (hG := hG))
    (wp_record : Recorder.record.spec (GF := GF) (hG := hG))
    (wp_drain : ∀ [StorageModel GF], Cluster.drain.spec (GF := GF) (hG := hG))
    (wp_run : ∀ [StorageModel GF], Cluster.run.spec (GF := GF) (hG := hG))
    (wp_deliver : ∀ [StorageModel GF], Cluster.deliver.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (h_alloc : clusterAllocFacts.law (GF := GF))
    (h_mint : propMint.law (GF := GF))
    (h_open : raftState_open_rn.law (GF := GF))
    (h_cmt : ∀ [StorageModel GF], rawNode_committed.law (GF := GF) (hG := hG))
    (h_recs : ∀ [StorageModel GF], rawNode_logRecs.law (GF := GF) (hG := hG)) :
    RunCluster.spec (GF := GF) (hG := hG) := by
  intro _ Hfits cfg Hcok
  wp_start as Htok
  ihave #Hsy : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  obtain ⟨HN3, HT0⟩ := Hcok
  have Hrb : receiptBound GF ≤ 2 ^ 64 - 2 := by unfold antRunFits at Hfits; omega
  try wp_auto
  -- the stop channel, a broadcast
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsch, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsch Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  try wp_auto
  -- the cluster's fields
  icases typedPointsto_split _ _ _ $$ «$r0» with Hcl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcl with ⟨Fcfg, Frec, Fnodes, Fstop, FnWg, FnetWg, -⟩
  generalize «$r0_ptr» = cl
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Fcfg with #Fcfg
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Frec with #Frec
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Fstop with #Fstop
  ihave Hcf := typedPointsto_split _ _ _ $$ Fcfg
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcf with ⟨#CNodes, -⟩
  -- the configuration's fields, read-only
  icases typedPointsto_split _ _ _ $$ cfg with Hcf0
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcf0 with ⟨CNodes0, CSettle, CTick, -⟩
  ipersist CNodes0
  ipersist CSettle
  ipersist CTick
  -- the storage registry
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := AntStorRecT) with ⟨%γreg, Hreg⟩
  letI : AntStor GF := ⟨γreg⟩
  imod inv_alloc antStorN ⊤ antStorInvBody $$ [Hreg] with #HstInv
  · inext
    iunfold antStorInvBody
    iexists ∅
    iframe Hreg
    iapply (BigSepM.bigSepM_empty).2; iempintro
  ihave #HstInv' : antStorInv (GF := GF) $$ []
  · iunfold antStorInv; iexact HstInv
  letI : StorageModel GF := antStorageModelNC
  -- the run's names, the recorder
  imod antGhosts_alloc (GF := GF) with ⟨%strm, %sent, %view, %live, Hs1, Hs2, V0a, V0b, V1a, V1b,
    V2a, V2b, L0, L1, L2, Hsa, #Hslb⟩
  icases typedPointsto_split _ _ _ $$ «$v1» with Hrc
  simp only [TypedPointsto.typedPointstoDef]
  icases Hrc with ⟨Rmu, Rev, -⟩
  imod receipt_zero (GF := GF) with Hr0
  imod sync.init_Mutex (recLockInv strm «$v1_ptr») ⊤ _ $$ Rmu [Rev Hs2 Hr0] with #Hrec
  · inext
    iunfold recLockInv
    iexists slice.nil, []
    iframe Rev Hs2
    isplitr
    · iunfold AntCheck.eventsRO
      iexists []
      isplitr
      · iapply ownSlice_nil
      iapply (BigSepL2.bigSepL2_nil).2; iempintro
    isplitr
    · iapply ownSliceCap_nil
    iExactEq Hr0; simp
  ihave #HisRec : isRecorder strm «$v1_ptr» $$ []
  · iunfold isRecorder; iexact Hrec
  -- raft's cluster
  imod h_alloc (nroot.@"raft") [W64 1, W64 2, W64 3] ⊤ Hrb (by simp) (by decide) (by decide)
    (by decide) with ⟨%γr, %Hγ, %Hnm, Hops, #Hcl, #Hca, Hvs⟩
  obtain ⟨Hdup, Hbl, Hmd, Hns, Htr⟩ := Hγ
  obtain ⟨Hcfg3, Hboot0, HreNs, HreTr, HreMd⟩ := Hnm
  imod opsInv_alloc γr [] ⊤ $$ Hops with #Hopsi
  ihave #Hrfit := readyFits_intro (GF := GF) γr (nroot.@"raft")
    (by rw [Hbl]; unfold antRunFits at Hfits; omega)
  ihave #Hlog := antLogger_isLogger (GF := GF)
  -- the voters
  imod receipt_zero (GF := GF) with Hrv0
  ihave IHv : iprop(∃ (k : w64) (sl : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "voters" ∷ voters_ptr ↦ sl ∗ "Hvr" ∷ ⧗ (uint.nat k - 1) ∗
      "Hsl" ∷ sl ↦* ((List.range (uint.nat k - 1)).map fun j : Nat => W64 ((j : Int) + 1)) ∗
      "Hcap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗ "%Hk" ∷ ⌜1 ≤ uint.Z k ∧ uint.Z k ≤ 4⌝)
    $$ [i voters Hrv0]
  · iexists W64 1, zero_val GoSlice
    iframe i voters
    rw [show uint.nat (W64 1) - 1 = 0 from rfl]
    isplitl [Hrv0]
    · iexact Hrv0
    isplitl []
    · simp only [List.range_zero, List.map_nil]; iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> decide
  wp_for IHv
  wp_if_destruct
  · try wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint64) [k]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.uint64 #k)] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Htmp, -⟩
    wp_take_receipt as Hvr1
    wp_apply wp_slice_append (V := w64) (t := go.uint64) sl _ _ [k] (DFrac.own 1)
      $$ [Hsl Hcap Htmp] as %sl' ⟨Hsl', Hcap', -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    have Hle : uint.Z k ≤ 3 := by rw [HN3] at Hif; word
    iexists k + W64 1, sl'
    have Hk1 : uint.nat (k + W64 1) - 1 = (uint.nat k - 1) + 1 := by word
    have HkW : W64 (((uint.nat k - 1 : Nat) : Int) + 1) = k := by word
    rw [Hk1, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [HkW]
    iframe
    isplitl [Hvr Hvr1]
    · iapply (receipt_add (GF := GF) _ 1).2; iframe Hvr Hvr1
    ipureintro; constructor <;> word
  · have Hk3 : uint.nat k - 1 = 3 := by
      have : ¬ uint.Z k ≤ 3 := by intro h; apply Hif; rw [HN3]; word
      word
    rw [Hk3]
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil]
    try wp_auto
    imod ownSlice_persist sl _ _ $$ Hsl with #Hsl
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ voters with #voters
    -- the nodes
    imod receipt_zero (GF := GF) with Hrz
    ihave IHn : iprop(∃ (k : w64) (nsl : GoSlice) (ds : List (Loc × ChanNames)),
        "i" ∷ i_ptr ↦ k ∗
        "Fnodes" ∷ cl.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster, go!"nodes"] ↦ nsl ∗
        "Hnsl" ∷ nsl ↦* ds.map Prod.fst ∗ "Hncap" ∷ ownSliceCap Loc nsl (DFrac.own 1) ∗
        "Hdone" ∷ ([∗list] j ↦ d ∈ ds, nodeMade γr d.1 (finOf j) ∗ nodeChanOwn d.1 d.2) ∗
        "Htodo" ∷ ([∗list] id ∈ [W64 1, W64 2, W64 3].drop (uint.nat k - 1),
          raftState γr id RaftState.init ∗ nodeVacant γr id) ∗
        "Hrc" ∷ ⧗ (2 * ds.length) ∗
        "%Hk" ∷ ⌜1 ≤ uint.Z k ∧ uint.Z k ≤ 4 ∧ ds.length = uint.nat k - 1⌝)
      $$ [i Fnodes Hvs Hrz]
    · iexists W64 1, zero_val GoSlice, []
      iframe i Fnodes
      rw [show uint.nat (W64 1) - 1 = 0 from rfl, List.drop_zero]
      iframe Hvs
      isplitl []
      · simp only [List.map_nil]; iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · iapply (BigSepL.bigSepL_nil).2; iempintro
      isplitl [Hrz]
      · iExactEq Hrz; simp
      ipureintro; exact ⟨by decide, by decide, rfl⟩
    wp_for IHn
    wp_if_destruct
    · have Hle : uint.Z k ≤ 3 := by
        have h : uint.Z k ≤ uint.Z cfg.Nodes' := by simpa using Hif
        rw [HN3] at h; exact h
      wp_apply wp_NewMemoryStorage false as %ms %γs ⟨%Hsz, #Hlock, #Hlog0, Hend, -, Hmeta, Hfresh⟩
      try wp_auto
      obtain ⟨Hdrop, Hk1, Hs1, Hs4, HkW, Hkk, Hkm, Hk3⟩ := rc_step k Hk.1 Hle
      -- the wrapper, registered
      icases typedPointsto_split _ _ _ $$ «$v3» with Hbs
      simp only [TypedPointsto.typedPointstoDef]
      icases Hbs with ⟨Sms, Svs, -⟩
      ipersist Svs
      imod antStor_register «$v3_ptr» ms γs ⊤ CoPset.subseteq_top Hsz $$ HstInv' Sms with #Hsrec
      ihave #Hbrec : bootStorRec «$v3_ptr» ms [W64 1, W64 2, W64 3] $$ []
      · iunfold bootStorRec
        iexists sl
        iframe Svs
        isplitr
        · iapply antStorRec_ms $$ Hsrec
        iExactEq Hsl; rfl
      rw [Hdrop]
      icases Htodo with ⟨⟨Hrs, Hvac⟩, Htodo⟩
      imod nodeVacant_arm γr k ⊤ $$ Hvac with ⟨%x, Hvac, -⟩
      ihave Hrst := ant_restartStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
        wp_Entries «$v3_ptr» ms [W64 1, W64 2, W64 3] γs γr
        (fun K => iprop(memStorMeta ms γs hsZero ∗ memStorInvP ms γs (antJ γr K))) Htr Hmd
        $$ Hpkg Hsrec Hbrec Hlock Hlog0 Hend Hmeta Hfresh []
      · iintro %K Hm Hi
        iframe Hm Hi
      wp_apply (wp_NewRawNode γr (nroot.@"raft") «$r0_ptr» (antConfig k «$v3_ptr»)
          ⟨github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger.ty,
            #(zero_val github_com.mit_pdos.etcd_grove.examples.raft.antithesis.quietLogger)⟩
          ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty,
            #«$v3_ptr»⟩ [W64 1, W64 2, W64 3]
          (fun K => iprop(memStorMeta ms γs hsZero ∗ memStorInvP ms γs (antJ γr K))) (snapshotValid γr)
          (fun _ => .rfl) (antConfig_valid k «$v3_ptr» Hk.1 Hle) rfl rfl
          (by show sint.Z (W64 256) < 2 ^ 62; decide) rfl rfl rfl
          (Or.inr (by show W64 1048576 ≠ W64 0; decide)) rfl (fun h => absurd Hmd h) rfl Hbl (by decide) Hns TraceLoggerOk_nil
          Htr ⟨rfl, rfl⟩ ⟨Hcfg3, Hkm⟩ x)
        $$ [«$r0» Hrst Hvac Hrs] as %rn %err ⟨%Herr, %sn, %g, %K, Hrn, Hgv, Hsf, Hrs, HF⟩
      · iframe Hlog Hcl Hrfit Hca Hvac Hrs
        isplitl [«$r0»]
        · iExactEq «$r0»; rfl
        isplitl [Hrst]
        · iExactEq Hrst; rfl
        iapply antStor_storCapF
      subst Herr
      wp_take_receipt as Hr1
      wp_apply wp_Name
      wp_apply (chan.wp_make2 (V := H.input) (W64 1024)) as %ch %γch ⟨#Hich, %_, Hoch⟩
      · ipureintro; constructor <;> decide
      try wp_auto
      icases typedPointsto_split _ _ _ $$ «$r0» with Hnd
      simp only [TypedPointsto.typedPointstoDef]
      icases Hnd with ⟨Nid, Nname, Nrn, Nst, Nin, Nrole, Nterm, Nvote, Ncommit, Ncause, Napp, -⟩
      ipersist Nid
      ipersist Nname
      ipersist Nrn
      ipersist Nst
      ipersist Nin
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := Loc)
        (t := go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)
        [«$r0_ptr»]
      wp_auto
      rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)
        #«$r0_ptr»)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Htmp, -⟩
      wp_take_receipt as Hr2
      wp_apply wp_slice_append (V := Loc)
          (t := go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)
          nsl _ _ [«$r0_ptr»] (DFrac.own 1)
        $$ [Hnsl Hncap Htmp] as %nsl' ⟨Hnsl', Hncap', -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, nsl', ds ++ [(«$r0_ptr», γch)]
      rw [Hk1]
      iframe
      isplitl [Hnsl']
      · iExactEq Hnsl'; simp
      isplitl [Hrn Hgv Hsf Hrs HF Nrole Nterm Nvote Ncommit Ncause Napp Hoch]
      · iapply (BigSepL.bigSepL_cons).2
        isplitl
        · simp only [Nat.zero_add]
          rw [Hk.2.2]
          icases HF with ⟨Hmeta, Hinvp⟩
          isplitl [Hmeta Hrn Hgv Hsf Hrs Nrole Nterm Nvote Ncommit Ncause Napp]
          · iunfold nodeMade
            rw [HkW]
            iexists rn, ms, «$v3_ptr», γs, sn, x, g
            iframe Nid Nname Nrn Nst Hbrec Hsrec Hlock Hmeta Hgv Hsf Hrs Nrole
            isplitr
            · ipureintro; exact Hsz
            isplitl [Hrn]
            · iExactEq Hrn; rfl
            isplitl [Nterm]
            · iExactEq Nterm; rfl
            isplitl [Nvote]
            · iExactEq Nvote; rfl
            isplitl [Ncommit]
            · iExactEq Ncommit; rfl
            isplitl [Napp]
            · iExactEq Napp; rfl
            iExactEq Ncause; rfl
          iunfold nodeChanOwn
          iexists ch
          iframe Nin Hich Hoch
        iapply (BigSepL.bigSepL_nil).2; iempintro
      isplitl [Hrc Hr1 Hr2]
      · rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
        iapply (receipt_add (GF := GF) _ _).2
        iframe Hrc
        iapply (receipt_add (GF := GF) 1 1).2
        iframe Hr1 Hr2
      ipureintro
      refine ⟨Hs1, Hs4, ?_⟩
      rw [List.length_append, List.length_singleton, Hk.2.2, Hkk]
    · -- the three nodes made
      have Hk4 : uint.nat k - 1 = 3 := by
        have h : ¬ uint.Z k ≤ uint.Z cfg.Nodes' := by simpa using Hif
        rw [HN3] at h
        exact rc_end k Hk.2.1 h
      have Hdl : ds.length = 3 := by rw [Hk.2.2, Hk4]
      obtain ⟨d0, d1, d2, rfl⟩ : ∃ d0 d1 d2, ds = [d0, d1, d2] := by
        match ds, Hdl with
        | [d0, d1, d2], _ => exact ⟨d0, d1, d2, rfl⟩
      obtain ⟨n0, γch0⟩ := d0
      obtain ⟨n1, γch1⟩ := d1
      obtain ⟨n2, γch2⟩ := d2
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at *
      imod ownSlice_persist nsl _ _ $$ Hnsl with #Hnsl
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Fnodes with #Fnodes
      icases Hdone with ⟨⟨M0, C0⟩, ⟨M1, C1⟩, ⟨M2, C2⟩, -⟩
      ihave M0 : nodeMade γr n0 0 $$ [M0]
      · iExactEq M0; rfl
      ihave M1 : nodeMade γr n1 1 $$ [M1]
      · iExactEq M1; rfl
      ihave M2 : nodeMade γr n2 2 $$ [M2]
      · iExactEq M2; rfl
      imod nodeMade_facts h_cmt h_recs γr n0 0 $$ M0 with ⟨M0, #Hcmt0, #Hlr0⟩
      -- the wait groups
      imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ FnWg with ⟨%γnw, Hnw⟩
      imod sync.join.init _ γnw $$ Hnw with Hadder
      imod sync.init_WaitGroup (antNetN.@"wg") _ $$ FnetWg with ⟨%γwg, Hwg⟩
      imod nj_init antNetN _ γwg ⊤ $$ Hwg with ⟨%γnj, Had⟩
      icases njAdder_isNetJoin antNetN _ γnj 1 $$ Had with ⟨Had, #Hnj⟩
      -- the run's names
      obtain ⟨γ, rfl, rfl, rfl, rfl, rfl, rfl, h0, h1, h2, rfl⟩ : ∃ γ : AntNames, γ.raft = γr ∧
          γ.strm = strm ∧ γ.view = view ∧ γ.live = live ∧ γ.sent = sent ∧ γ.net = γnj ∧
          γ.inCh 0 = γch0 ∧ γ.inCh 1 = γch1 ∧ γ.inCh 2 = γch2 ∧ γ.stopCh = γsc :=
        ⟨⟨γr, strm, view, live, sent, γnj, fin3 γch0 γch1 γch2, γsc⟩, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl⟩
      subst h0 h1 h2
      imod antInv_alloc γ ⊤ $$ Hs1 V0a V1a V2a Hsa Hcmt0 Hlr0 with #Hinv
      -- the nodes' input bags and records
      iunfold nodeChanOwn at C0 C1 C2
      icases C0 with ⟨%ch0, #Nin0, #Hich0, Hoch0⟩
      icases C1 with ⟨%ch1, #Nin1, #Hich1, Hoch1⟩
      icases C2 with ⟨%ch2, #Nin2, #Hich2, Hoch2⟩
      imod start_bag (V := H.input) (inputOk γ 0) (ChanState.Buffered []) ch0 (γ.inCh 0) trivial
        $$ Hich0 Hoch0 with #Hbag0
      imod start_bag (V := H.input) (inputOk γ 1) (ChanState.Buffered []) ch1 (γ.inCh 1) trivial
        $$ Hich1 Hoch1 with #Hbag1
      imod start_bag (V := H.input) (inputOk γ 2) (ChanState.Buffered []) ch2 (γ.inCh 2) trivial
        $$ Hich2 Hoch2 with #Hbag2
      have hfacts : γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = AntSim.voters3 ∧
          γ.raft.raftNames.maxData = none ∧ γ.raft.raftNames.reBoot = [] ∧
          (↑(raftN γ.raft.raftNames) : CoPset) ⊆ ⊤ \ ↑antN :=
        ⟨HreTr, Hcfg3, HreMd, Hboot0, by unfold raftN; rw [HreNs]; exact raftNs_mask⟩
      ihave V0b : viewFrag γ 0 antView0 $$ [V0b]
      · iunfold viewFrag; iexact V0b
      ihave L0 : nodeLive γ 0 $$ [L0]
      · iunfold nodeLive; iexact L0
      ihave V1b : viewFrag γ 1 antView0 $$ [V1b]
      · iunfold viewFrag; iexact V1b
      ihave L1 : nodeLive γ 1 $$ [L1]
      · iunfold nodeLive; iexact L1
      ihave V2b : viewFrag γ 2 antView0 $$ [V2b]
      · iunfold viewFrag; iexact V2b
      ihave L2 : nodeLive γ 2 $$ [L2]
      · iunfold nodeLive; iexact L2
      ihave #Hslb' : sentLb γ [] $$ []
      · iunfold sentLb; iexact Hslb
      icases nodeMade_own (GF := GF) h_open cl γ 0 n0 hfacts $$ M0 V0b L0 Hslb' with ⟨⟨#Nid0, #Nname0⟩, O0⟩
      icases nodeMade_own (GF := GF) h_open cl γ 1 n1 hfacts $$ M1 V1b L1 Hslb' with ⟨⟨#Nid1, #Nname1⟩, O1⟩
      icases nodeMade_own (GF := GF) h_open cl γ 2 n2 hfacts $$ M2 V2b L2 Hslb' with ⟨⟨#Nid2, #Nname2⟩, O2⟩
      ihave #R0 : nodeRO γ n0 0 $$ []
      · iunfold nodeRO; iexists ch0; iframe Nid0 Nname0 Nin0 Hbag0
      ihave #R1 : nodeRO γ n1 1 $$ []
      · iunfold nodeRO; iexists ch1; iframe Nid1 Nname1 Nin1 Hbag1
      ihave #R2 : nodeRO γ n2 2 $$ []
      · iunfold nodeRO; iexists ch2; iframe Nid2 Nname2 Nin2 Hbag2
      ihave #Hro : clusterRO cl [n0, n1, n2] (W64 3) $$ []
      · iunfold clusterRO
        iexists nsl
        iframe Fnodes Hnsl
        rw [← HN3]; iexact CNodes
      ihave #Hc : antCluster cl γ $$ []
      · iunfold antCluster
        iexists cfg, «$v1_ptr», [n0, n1, n2], sc
        iframe Fcfg Frec HisRec Fstop Hunk Hnj Hinv Hro
        isplitr
        · ipureintro; exact ⟨HN3, HT0⟩
        isplitr
        · ipureintro; rfl
        isplitr
        · iExactEq R0; rfl
        isplitr
        · iExactEq R1; rfl
        isplitr
        · iExactEq R2; rfl
        ipureintro; exact Hfits
      -- the boot drains
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ c with #c
      ihave Hpool : ⧗ (3 + (3 + 3)) $$ [Hvr Hrc]
      · iapply (receipt_add (GF := GF) 3 (3 + 3)).2
        iframe Hvr
        iExactEq Hrc; rfl
      icases (receipt_add (GF := GF) 3 (3 + 3)).1 $$ Hpool with ⟨Hq0, Hpool⟩
      icases (receipt_add (GF := GF) 3 3).1 $$ Hpool with ⟨Hq1, Hq2⟩
      wp_apply (wp_slice_for_range_drain (V := Loc) _ nsl [n0, n1, n2] DFrac.discard _
        (fun i => iprop(threadTok ∗ netAdder cl γ 1 ∗ (∃ x : Loc, n_ptr ↦ x) ∗ bootP cl γ n0 n1 n2 i)))
        $$ Hnsl [Htok Had n O0 O1 O2 Hq0 Hq1 Hq2]
      · iframe Htok
        isplitl [Had]
        · iunfold netAdder; iexact Had
        isplitl [n]
        · iexists _; iexact n
        unfold bootP bootA
        simp (config := { decide := true }) only [ite_true, ite_false]
        iframe O0 O1 O2 Hq0 Hq1 Hq2 R0 R1 R2
      · imodintro
        iintro %i %x %hx ⟨Htk, Had, ⟨%x0, Hn⟩, HP⟩ #Hs
        have hi : i < 3 := by
          have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
        have hxe : x = [n0, n1, n2][i]! := by
          rw [getElem!_pos [n0, n1, n2] i (by simpa using hi)]
          exact (List.getElem?_eq_some_iff.1 hx).2.symm
        subst hxe
        icases bootP_split cl γ n0 n1 n2 i hi $$ HP with ⟨HA, Hback⟩
        iunfold bootA at HA
        icases HA with ⟨HO, Hr3, #HR⟩
        ihave #HR' := HR
        iunfold nodeRO at HR'
        icases HR' with ⟨%chx, #Hxid, #Hxname, #Hxin, #Hxbag⟩
        wp_take_op_receipt as Hb1
        wp_take_receipt as Hb2
        wp_apply wp_names as %vsl Hvsl
        try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoString) (t := go.string) []
        wp_auto
        rw [show go.arrayLiteralSize ([] : List keyed_element) = 0 from rfl]
        isplitl []
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        imod ownSlice_persist _ _ _ $$ Hosl with #Hosl
        try wp_auto
        ipersist «$a0»
        iunfold AntCheck.strsRO at Hvsl
        ipersist Hvsl
        ihave #Hvsl3 : vsl ↦*□ AntSim.namesL 3 $$ []
        · iExactEq Hvsl; rw [HN3]; rfl
        ihave #Hev : AntCheck.eventRO «$a0_ptr» (AntSim.evBoot (AntSim.nodeId (finOf i))) $$ []
        · iunfold AntCheck.eventRO
          iexists _
          iframe «$a0»
          simp only [AntSim.evBoot, AntCheck.fieldRO]
          isplitr
          · ipureintro
            simp only [AntCheck.fieldRel, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.hasBit,
              AntCheck.fB, AntCheck.fA, AntCheck.fBy,
              AntCheck.fRole, AntCheck.fTerm, AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst,
              AntCheck.fLastIndex, AntCheck.fLastTerm, AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW,
              AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
            and_intros <;> first | rfl | decide
          simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing,
            AntCheck.fMsg, AntCheck.fCause]
          iunfold AntCheck.strsRO
          iframe Hvsl3 Hosl
          ipureintro
          and_intros <;> decide
        icases nodeOwn_take cl γ (finOf i) _ antView0 _ $$ HO with ⟨Hv, Hl, Hput⟩
        ihave #Hfx := factsExt_none (GF := GF) γ
        ihave HAU := report_au γ (finOf i) antView0 antView0 (AntSim.evBoot (AntSim.nodeId (finOf i)))
          [] [] (fun _ => True) (boot_step GF Hfits (finOf i)) $$ [Hv Hl]
        · iframe Hinv Hslb' Hfx Hv Hl
        ihave Hrc5 : ⧗ (AntSim.evBoot (AntSim.nodeId (finOf i))).weight $$ [Hb1 Hb2 Hr3]
        · rw [show (AntSim.evBoot (AntSim.nodeId (finOf i))).weight = 1 + (1 + 3) by
            simp [AntCheck.Event.weight, AntCheck.Event.size, AntSim.evBoot, AntSim.namesL_three]]
          iapply (receipt_add (GF := GF) 1 (1 + 3)).2
          iframe Hb1
          iapply (receipt_add (GF := GF) 1 3).2
          iframe Hb2 Hr3
        wp_apply wp_record γ.strm «$v1_ptr» «$a0_ptr» (AntSim.evBoot (AntSim.nodeId (finOf i))) _
          $$ [$Hpkg $HisRec $Hev $Hrc5 $HAU] as ⟨Hv, Hl, -⟩
        ihave HO := Hput $$ Hv Hl
        try wp_auto
        have wd := wp_drain cl γ ([n0, n1, n2][i]!) (finOf i) antView0 [] pInit 1
        rw [show antView0.byE = go!"boot" from rfl] at wd
        wp_apply wd $$ [$Hpkg $Hc $HR $HO $Had $Htk] as %v' ⟨HO, Had, Htk, %Hby⟩
        ihave HO := nodeOwn_drained_idle cl γ (finOf i) _ v' (by rw [Hby]; decide) $$ HO
        ihave HP := Hback $$ [HO]
        · iunfold bootB; iexists v'; iexact HO
        try wp_auto
        iframe Hs
        isplitr
        · ipureintro; rfl
        iframe Htk HP
        isplitl [Had]
        · iexact Had
        iexists _; iexact Hn
      -- the node goroutines
      iintro ⟨Htok, Had, -, HP⟩ #-
      icases bootP_three cl γ n0 n1 n2 $$ HP with ⟨B0, B1, B2⟩
      ihave HG := go_start cl γ n0 n1 n2 $$ [B0 B1 B2 Had]
      · iframe B0 B1 B2 Had R0 R1 R2
      ihave Hadder := sync.join.ownAdder_wand
        (tri (fun _ => iprop(True)) (fun j => nodeExit cl γ (finOf j) (antQ j)) 0) _ _ _ $$ [] Hadder
      · iintro -
        unfold tri
        simp (config := { decide := true }) only [ite_false]
        isplitr
        · itrivial
        isplitr
        · itrivial
        itrivial
      try wp_auto
      wp_apply (wp_slice_for_range_drain (V := Loc) _ nsl [n0, n1, n2] DFrac.discard _
        (fun i => iprop(threadTok ∗ (∃ x : Loc, n_ptr ↦ x) ∗
          sync.join.ownAdder (cl.[H.Cluster, go!"nodesWg"]) (W32 (i : Int))
            (tri (fun _ => iprop(True)) (fun j => nodeExit cl γ (finOf j) (antQ j)) i) ∗
          tri (goA cl γ [n0, n1, n2]) (fun _ => iprop(True)) i)))
        $$ Hnsl [Htok n Hadder HG]
      · iframe Htok HG
        isplitl [n]
        · iexists _; iexact n
        iExactEq Hadder; rfl
      · imodintro
        iintro %i %x %hx ⟨Htk, ⟨%x0, Hn⟩, Hadder, HP⟩ #Hs
        have hi : i < 3 := by
          have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
        have hxe : x = [n0, n1, n2][i]! := by
          rw [getElem!_pos [n0, n1, n2] i (by simpa using hi)]
          exact (List.getElem?_eq_some_iff.1 hx).2.symm
        subst hxe
        obtain ⟨hw1, hw2⟩ := w32_step i hi
        icases tri_split _ _ i hi $$ HP with ⟨HA, Hback⟩
        iunfold goA at HA
        iunfold bootB at HA
        icases HA with ⟨⟨%v, HO⟩, Hq, #HR⟩
        try wp_auto
        wp_apply (sync.join.WaitGroup.wp_Add_of wp_Add (nodeExit cl γ (finOf i) (antQ i)) _ _
            (W32 (i : Int))) $$ [Hadder] as ⟨Hadder, Hdone⟩
        · iframe Hadder
          ipureintro; exact hw1
        try wp_auto
        wp_apply wp_fork_tok_body $$ [HO Hq Hdone]
        · iintro Htt
          wp_apply (wp_run cl γ ([n0, n1, n2][i]!) (finOf i) v (antQ i))
            $$ [$Hpkg $Hc $HR $HO $Hq $Htt $Hdone] as Htt
          iframe Htt
          ipureintro; simp
        try wp_auto
        iframe Hs
        isplitr
        · ipureintro; rfl
        iframe Htk
        isplitl [Hn]
        · iexists _; iexact Hn
        rw [hw2]
        isplitl [Hadder]
        · iapply sync.join.ownAdder_wand $$ [] Hadder
          iintro ⟨Hp, He⟩
          icases tri_split _ _ i hi $$ Hp with ⟨-, Hb⟩
          iapply Hb $$ He
        iapply Hback
        itrivial
      iintro ⟨Htok, -, Hadder, -⟩ #-
      try wp_auto
      -- the proposer's join
      imod sync.init_WaitGroup (antPropN.@"wg") _ $$ proposer with ⟨%γdw, #Hdwg, Hdwo, Hdww⟩
      wp_apply (joinN.wp_Add_of wp_Add antPropN _ γdw 1 (by decide))
        $$ [$Hsy $Hdwg $Hdwo $Hdww] as ⟨%γj, Hd, Hdw⟩
      try wp_auto
      -- the proposer: until it sees the stop channel closed
      wp_apply wp_fork $$ [Hd]
      · try wp_auto
        ihave IHp : iprop(∃ kk : w64, "k" ∷ k_ptr ↦ kk) $$ [k]
        · iexists _; iexact k
        wp_for IHp
        wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
            iprop(jNDones antPropN proposer_ptr γj 1 ∗ k_ptr ↦ kk) $$ [] [Hd k] []
        · iapply BigSepL2.bigSepL2_singleton.2
          iintro ⟨Hd, k⟩
          simp only [chan.nonblockingAltClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γ.stopCh
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply ownBroadcastChan_is_chan $$ Hunk
          iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hunk
          isplit
          · -- the run stops
            iintro -
            try wp_auto
            wp_apply joinN.wp_Done_of wp_Done antPropN _ γj $$ [$Hsy $Hd]
            try wp_auto
            wp_for_post
            ipureintro; simp
          · iintro -
            iframe Hd k
        · iframe Hd k
        -- not stopped: a proposal to a random node
        iintro ⟨Hd, k⟩ -
        try wp_auto
        wp_apply wp_below cfg.Nodes' (by rw [HN3]; decide) $$ [$Hpkg] as %b %Hb
        rw [HN3] at Hb
        ihave %Hlen := ownSlice_len _ _ _ $$ Hnsl
        obtain ⟨Hp0, Hp1, Hp2, Hp3⟩ := ant_pick b nsl.len Hb Hlen.1 Hlen.2
        try wp_auto
        simp only [show 0 ≤ sint.Z b ∧ sint.Z b < sint.Z nsl.len from ⟨Hp0, Hp1⟩, _root_.and_self,
          ↓reduceIte]
        wp_apply wp_load_slice_index nsl (sint.Z b) _ DFrac.discard ([n0, n1, n2][uint.nat b]!) Hp0
          $$ [] as -
        · iframe Hnsl
          ipureintro
          rw [Hp2, getElem!_pos [n0, n1, n2] (uint.nat b) (by simpa using Hp3)]
          exact List.getElem?_eq_getElem _
        ihave #HRb : nodeRO γ ([n0, n1, n2][uint.nat b]!) (finOf (uint.nat b)) $$ []
        · iapply nodeRO_at γ n0 n1 n2 (uint.nat b) Hp3
          iframe R0 R1 R2
        try wp_auto
        wp_apply wp_FormatUint kk (W64 10) (by decide) (by decide) $$ [$Hsc]
        try wp_auto
        wp_apply wp_string_to_bytes as %bsl ⟨Hbs, -⟩
        imod ownSlice_persist bsl _ _ $$ Hbs with #Hbs
        imod propOk_mint h_mint γ (nroot.@"raft") ([118#8] ++ internal.strconv.fmtUint kk (W64 10)) ⊤
          CoPset.subseteq_top opsNs_mask Hdup HreMd $$ Hcl Hopsi with Hpo
        try wp_auto
        wp_apply wp_deliver cl γ ([n0, n1, n2][uint.nat b]!) (finOf (uint.nat b)) _
          $$ [$Hpkg $Hc Hpo]
        · iframe HRb
          iunfold inputOk
          iright
          isplitr
          · ipureintro; rfl
          iexists _
          iframe Hbs Hpo
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
      try wp_auto
      -- the stop
      wp_apply wp_Sleep
      try wp_auto
      wp_apply wp_broadcast_chan_close sc γ.stopCh iprop(True) $$ [$Hpend] as -
      · iintro !>; itrivial
      try wp_auto
      -- the proposer done
      wp_apply joinN.wp_Wait_of wp_Wait antPropN _ γj $$ [$Hsy $Hdw]
      try wp_auto
      -- the node goroutines done
      wp_apply (lc := 1) (sync.join.WaitGroup.wp_Wait_of wp_Wait _ _ _) $$ [$Hsy $Hadder]
        as ⟨Hex, -⟩
      imod lc_fupd_elim_later $$ Hlc1 Hex with Hex
      icases go_end cl γ $$ Hex with ⟨L0, L1, L2, Had⟩
      iunfold netAdder at Had
      imod njClose antNetN _ γ.net $$ Had with ⟨Hw0, #Hnj'⟩
      -- the run is over
      imod antInv_close γ $$ Hinv L0 L1 L2 with ⟨%evs, Hdone, %Hacc⟩
      try wp_auto
      -- the network's goroutines done
      wp_apply netJoin.wp_Wait_of wp_Wait antNetN _ γ.net $$ [$Hsy $Hw0 $Hnj']
      try wp_auto
      iapply HΦ
      iframe Htok
      iunfold runOver
      iexists «$v1_ptr», γ.strm, evs
      iframe Frec HisRec Hdone
      isplitr
      · rw [← HN3]; iexact CNodes
      ipureintro; exact Hacc

end proof

end AntHarness
end EtcdGrove
end Perennial
