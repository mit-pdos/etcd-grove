/-
Lean-first (no Rocq counterpart). #33 S4, `Cluster.drain`: **the numbers of a `Ready`** below the
binding's `numBound` (`2 ^ 61`), what `NetFacts` asks of a message `send` hands over, the `send`
report's `NumsOk`, and `MemoryStorage.Append`'s `k + es.length ≤ 2 ^ 61`.

- `rawNode_stateNums`: a node's log, commit and entries' indices below `2 ^ 61`: its last entry's
  record carries a time receipt for its index (`logRecs_lookup`, `isEntryR_receipt`), below the
  receipts' bound (`preceipt_lt`), which `antRunFits` puts below `2 ^ 61 - 3`; in a cluster with no
  bootstrap log (`γ.reBoot = []`). Its entries' terms are a premise (raft has no law for them yet:
  see the report).
- with `AntSim.readyMsgNums` (`Sim/MsgBounds.lean`): each message of the `Ready` within the bound;
  `msgNums_st` reads it back on the message's Go state (`absMsgOf`), as `NetFacts` states it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRunLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgBounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Pure -/

section pure
variable [GooseExts]

/-- A message's numbers on its Go state: the protocol reading (`absMsgOf`, not a snapshot) carries
the state's index, log term, commit and entries. -/
theorem msgNums_st {K : Int} {st : MsgSt} {q : Msg} (h : absMsgOf st = some q)
    (hns : q.ty ≠ .snap) (hq : AntSim.MsgNums K q) :
    uint.Z st.msg.Index' < K ∧ uint.Z st.msg.LogTerm' < K ∧ uint.Z st.msg.Commit' < K ∧
      ∀ e ∈ st.ents, uint.Z e.Term' < K ∧ uint.Z e.Index' < K := by
  unfold absMsgOf at h
  split at h
  · cases h
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact absurd rfl hns
  · cases h; exact hq

end pure

/-! ## A node's numbers, from its log's records -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A node's numbers below `2 ^ 61`** (`AntSim.StateNums`): no snapshot, its last index and commit
and its entries' indices, from its last entry's time receipt (no bootstrap log); its entries' terms
given (`hterm`). -/
theorem rawNode_stateNums (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_ns : rawNode_noSnap.law (GF := GF) (hG := hG))
    (h_recs : rawNode_logRecs.law (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat)
    (hboot : γ.reBoot = []) (hfit : antRunFits GF)
    (hterm : ∀ e ∈ ps.log, uint.Z e.Term' < 2 ^ 61) :
    ⊢ rawNode (GF := GF) γ rn id rs ps qs ip ==∗
      ⌜AntSim.StateNums (2 ^ 61) ps⌝ ∗ rawNode γ rn id rs ps qs ip := by
  iintro Hr
  icases h_wf _ _ _ _ _ _ _ $$ Hr with ⟨%Hwf, Hr⟩
  icases h_ns _ _ _ _ _ _ _ $$ Hr with ⟨%Hns, Hr⟩
  icases h_recs _ _ _ _ _ _ _ $$ Hr with ⟨#Hrecs, Hr⟩
  obtain ⟨hwf, hcl, -⟩ := Hwf
  unfold antRunFits at hfit
  -- the log's length is below the receipts' bound
  have hidx : ∀ (k : Nat) (e : EntryM), ps.log[k]? = some e → uint.Z e.Index' = (k : Int) + 1 := by
    intro k e he; have := hwf k e he; rw [base0_index] at this; push_cast at this; omega
  ihave Hlen : |==> ⌜(ps.log.length : Int) < 2 ^ 61⌝ $$ []
  · rcases Nat.eq_zero_or_pos ps.log.length with h0 | hpos
    · imodintro; ipureintro; rw [h0]; omega
    obtain ⟨e, he⟩ : ∃ e, ps.log[ps.log.length - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hi := hidx _ e he
    have hlt : uint.Z e.Index' < 2 ^ 64 := (uint_Z_lt _)
    icases logRecs_lookup γ ps.log _ e he (by omega) $$ Hrecs with ⟨%pt, -, #He⟩
    imod isEntryR_receipt γ e pt $$ He with #Hrc
    ihave %Hrb := preceipt_lt _ $$ Hrc
    imodintro
    ipureintro
    rw [hboot] at Hrb
    simp only [List.length_nil, Nat.sub_zero] at Hrb
    omega
  imod Hlen with %Hlen
  imodintro
  iframe Hr
  ipureintro
  have hlast : plogLastIndexZ base0 ps.log = (ps.log.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  refine ⟨by omega, Hns.1, by rw [hlast]; exact Hlen, by rw [hlast] at hcl; omega,
    fun e he => ⟨hterm e he, ?_⟩⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have := hidx k _ (List.getElem?_eq_getElem hk)
  omega

end ghost

end AntHarness
end EtcdGrove
end Perennial
