/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E (`node.drain`): **the numbers of a
`Ready`** below the binding's `numBound` (`2 ^ 61`), what `NetFacts` asks of a message `send` hands
over and the `send` report's `NumsOk` (S4's `DrainBounds.lean` and `loopRest_tc`, over raft's
B1 laws at a mode `md`).

- `rawNode_stateNums_b1`: a node's numbers (`AntSim.StateNums (2 ^ 61)`) and its term ceiling below
  `2 ^ 61`: the ceiling within the receipts' bound (`rnTermLB_rb`, `antRunFits`), the log's terms at
  most the node's term (`rawNode_logTerms`) at most the ceiling (`rawNode_term_tc`); the log's length
  from its last entry's time receipt (`logRecs_lookup`, `isEntryR_receipt`, `preceipt_lt`), past the
  bootstrap log of at most one entry.
- `readNums_noReads`, `causeNums_noReads`: without reads, the view's read requests' and the drain's
  cause's numbers, what `AntSim.readyMsgNums` asks besides `StateNums` (no read request is deferred
  or queued, `NodeFacts`; the network carries no `MsgReadIndex`, `MsgMask`; the cause's index and
  log term `ViewNormal`'s). With reads on neither is in the run's invariant yet (see the resume notes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Loop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgBounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Pure: without reads -/

section pure
variable [GooseExts]

/-- The bootstrap log has at most one entry. -/
theorem bootLog_length_le (R : AntSim.RunCfg) : (AntSim.bootLog R).length ≤ 1 := by
  unfold AntSim.bootLog; split <;> simp

/-- **Without reads, the view's read requests are within any bound**: none deferred, a leader's
queue empty (`NodeFacts`). -/
theorem readNums_noReads {R : AntSim.RunCfg} {n : Fin R.N} {v : AntSim.NodeView} {K : Int}
    (hf : AntSim.NodeFacts R n v) (hr : R.md.reads = false) : AntSim.ReadNums K v.ps := by
  refine ⟨fun p hp => ?_, fun hl q hq => ?_⟩
  · rw [hf.pend0 hr] at hp; cases hp
  · rw [hf.roPend hr hl] at hq; cases hq

/-- **Without reads, the drain's cause's numbers**: its index and log term (`ViewNormal`), not a
proposal, and no `MsgReadIndex` (the network's messages are under the mask, `MsgMask`). -/
theorem causeNums_noReads {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg}
    {n : Fin R.N} {v : AntSim.NodeView} (hnet : AntSim.NetOk R S net)
    (hv : AntSim.NodeOk R dec S net n v) (hN : ViewNormal v) (hr : R.md.reads = false) :
    ∀ m, v.cause = some m → AntSim.InNums (2 ^ 61) m ∧ m.ty ≠ .propose ∧
      (m.ty = .readIndex → AntSim.MsgNums (2 ^ 61) m) := by
  intro m hm
  obtain ⟨-, hi, hl, hp⟩ := hN.2 m hm
  refine ⟨⟨hi, hl⟩, hp, fun hty => ?_⟩
  have hmn := (hv.cause m hm).1
  have hmask := hnet.2.2.2.2.1 m hmn
  exfalso
  rcases hmask.2.2.1 with h | h
  · unfold AntSim.NetTy at h
    rw [hty, hr] at h
    rcases h with h | h | h | h | h | h | ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> cases h
  · rw [hty] at h; cases h

end pure

/-! ## A node's numbers, from its log's records and the term budget -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A node's numbers below `2 ^ 61`** (`AntSim.StateNums`) and its term ceiling below `2 ^ 61`, at
a B1 mode: see the file header. -/
theorem rawNode_stateNums_b1 (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_ns : rawNode_noSnap.law (GF := GF) (hG := hG))
    (h_recs : rawNode_logRecs.law (GF := GF) (hG := hG))
    (h_lt : rawNode_logTerms.law (GF := GF) (hG := hG))
    (h_ttc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_rb : rnTermLB_rb.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (md : RnMode) (hs : md.snapshots = false) (hcc : md.confChanges = false)
    (hfw : md.forwarding = false) (has : md.async = false)
    (γ : Cluster) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (hboot : γ.raftNames.reBoot.length ≤ 1) (hfit : antRunFits GF) :
    ⊢ rnBudget γ -∗ rnTermLB γ rs.tc -∗ rawNode (GF := GF) γ.raftNames md rn id rs r qs ip ={⊤}=∗
      ⌜AntSim.StateNums (2 ^ 61) r.p ∧ uint.Z rs.tc < 2 ^ 61⌝ ∗ rnBudget γ ∗ rnTermLB γ rs.tc ∗
        rawNode γ.raftNames md rn id rs r qs ip := by
  iintro Hb Htl Hr
  haveI := h_bp γ
  haveI := h_tlp γ rs.tc
  ihave #Hb := Hb
  ihave #Htl := Htl
  icases h_wf md hs hcc hfw has _ _ _ _ _ _ _ $$ Hr with ⟨%Hwf, Hr⟩
  icases h_ns md hs hcc hfw has _ _ _ _ _ _ _ $$ Hr with ⟨%Hns, Hr⟩
  icases h_lt md hs hcc hfw has _ _ _ _ _ _ _ $$ Hr with ⟨%Hlt, Hr⟩
  icases h_ttc md hs hcc hfw has _ _ _ _ _ _ _ $$ Hr with ⟨%Httc, Hr⟩
  icases h_recs md hs hcc hfw has _ _ _ _ _ _ _ $$ Hr with ⟨#Hrecs, Hr⟩
  imod h_rb γ rs.tc ⊤ (by solve_ndisj) $$ Hb Htl with %Hrb
  obtain ⟨hwf, hcl, -⟩ := Hwf
  unfold antRunFits at hfit
  have htc : uint.Z rs.tc < 2 ^ 61 := by
    have : uint.Z rs.tc = (uint.nat rs.tc : Int) := by word
    omega
  have hidx : ∀ (k : Nat) (e : EntryM), r.p.log[k]? = some e → uint.Z e.Index' = (k : Int) + 1 := by
    intro k e he; have := hwf k e he; rw [base0_index] at this; push_cast at this; omega
  ihave Hlen : |==> ⌜(r.p.log.length : Int) < 2 ^ 61⌝ $$ []
  · rcases Nat.eq_zero_or_pos r.p.log.length with h0 | hpos
    · imodintro; ipureintro; rw [h0]; omega
    obtain ⟨e, he⟩ : ∃ e, r.p.log[r.p.log.length - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hi := hidx _ e he
    have hlt : uint.Z e.Index' < 2 ^ 64 := (uint_Z_lt _)
    icases logRecs_lookup γ.raftNames r.p.log _ e he (by omega) $$ Hrecs with ⟨%pt, -, #He⟩
    imod isEntryR_receipt γ.raftNames e pt $$ He with #Hrc
    ihave %Hrb' := preceipt_lt _ $$ Hrc
    imodintro
    ipureintro
    omega
  imod Hlen with %Hlen
  imodintro
  iframe Hr Hb Htl
  ipureintro
  have hlast : plogLastIndexZ base0 r.p.log = (r.p.log.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  refine ⟨⟨by omega, Hns.1, by rw [hlast]; exact Hlen, by rw [hlast] at hcl; omega,
    fun e he => ⟨?_, ?_⟩⟩, htc⟩
  · have := Hlt e he; omega
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have := hidx k _ (List.getElem?_eq_getElem hk)
    omega

end ghost

end AntHarness
end EtcdGrove
end Perennial
