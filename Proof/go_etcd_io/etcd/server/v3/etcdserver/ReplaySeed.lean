/- Relate the WAL suffix and the durable backend image to the same Raft log. -/
module
public import Proof.go_etcd_io.raft.v3.DurableLogView
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayCoverage

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

variable [GooseExts]

/-- The full committed prefix contains the same entry term as the compacted log wherever
the latter still has that index, including the compaction boundary. -/
theorem replayDurAgrees (S : RaftState) (fp : List EntryM) (l : List LogEntry)
    (hf : FullOk S.base fp) (hw : PlogWf S.base S.ents)
    (hp : l <+: strip ((fp ++ S.ents).take (uint.nat S.commit))) : DurAgrees S l := by
  intro i e hb he
  have hl := prefix_lookup_Some he hp
  simp only [strip, List.getElem?_map, List.getElem?_take] at hl
  by_cases hi : i < uint.nat S.commit
  · simp only [hi, ↓reduceIte] at hl
    cases hx : (fp ++ S.ents)[i]? with
    | none => simp [hx] at hl
    | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at hl
      subst e
      have hwf := full_wf S.base fp S.ents hf hw
      have hidx := hwf i x hx
      rw [base0_index] at hidx
      have heq : W64 ((i : Int) + 1) = x.Index' := by word
      rw [heq, ← full_term_at S.base fp S.ents x.Index' hf (by word)]
      apply plogTermAt_lookup _ _ _ i x hx
      rw [base0_index]; exact hidx
  · simp [hi] at hl

/-- Every retained log index above the bootstrap base has a term in the initial slice. -/
theorem replaySeed_pending (S : RaftState) (σ : StorContents) (A : List EntryModel)
    (hold : StorageHolds S σ) (hw : PlogWf S.base S.ents)
    (ordered : (σ.ents.map EntryModel.ofM).Pairwise (fun a b => uint.nat a.index < uint.nat b.index))
    (agree : DurAgrees S (A.map EntryModel.toLE)) :
    replayPending ((σ.ents.map EntryModel.ofM).foldl replayAddEntry []) A σ.b := by
  obtain ⟨layout, _, listed⟩ := replayFold_coverage [] _ (by simp [replayLayout]) ordered (by simp)
  refine ⟨layout, ?_⟩
  intro ci hn hci
  have hb := hold.1
  change uint.nat σ.base.index' < A.length at hn
  have hlt : uint.Z S.base.index' < uint.Z ci := by word
  have ht := replayImage_plogTerm A S ci (by omega) hci (by word) agree
  obtain ⟨e, he, hidx, hterm⟩ := plogTermAt_some_entry S.base S.ents ci _
    (PlogWf_wfR _ _ hw) ht hlt
  have hs : e ∈ σ.ents := by
    rw [hold.2.2.1, RaftState.entsFrom]
    let k := (uint.Z ci - uint.Z σ.base.index' - 1).toNat
    apply List.mem_of_getElem? (i := k)
    rw [List.getElem?_drop]
    have hk : (uint.Z σ.base.index' - uint.Z S.base.index').toNat + k =
        (uint.Z ci - uint.Z S.base.index' - 1).toNat := by
      dsimp [k]; have := uint_nat_eq σ.base.index'; omega
    rwa [hk]
  have covered := listed (EntryModel.ofM e) (List.mem_map_of_mem hs)
  change replayHasTerm _ e.Index' e.Term' at covered
  rwa [hidx, hterm] at covered

variable [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics] [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Extract the order required by the physical startup scan and identify every represented
term of an already committed image through the durable commit. -/
theorem replaySeed_facts (cl : Cluster) (id : w64) (N : Namespace) (S : RaftState)
    (σ : StorContents) (l : List LogEntry) (holds : StorageHolds S σ)
    (hc : l.length ≤ uint.nat S.commit) :
    isCluster (GF := GF) cl N ∗ raftState cl id S ∗ isCommittedLogLb cl l ⊢ |={⊤}=>
      raftState cl id S ∗ ⌜(σ.ents.map EntryModel.ofM).Pairwise
        (fun a b => uint.nat a.term ≤ uint.nat b.term ∧ uint.nat a.index < uint.nat b.index) ∧
        PlogWf S.base S.ents ∧ DurAgrees S l⌝ := by
  iintro ⟨#Hcl, Hstate, #Hl⟩
  imod raftState_logView cl id S N $$ [$Hcl $Hstate] with
    ⟨Hstate, %fp, %hf, %ordered, #Hcommit⟩
  ihave %hcmp := isCommittedLogLb_agree cl l (strip ((fp ++ S.ents).take (uint.nat S.commit))) $$ [$Hl $Hcommit]
  have hd : l <+: strip ((fp ++ S.ents).take (uint.nat S.commit)) := by
    rcases hcmp with h | h
    · exact h
    · have hlen : (strip ((fp ++ S.ents).take (uint.nat S.commit))).length = uint.nat S.commit := by
        simp only [strip, List.length_map, List.length_take, Nat.min_eq_left hf.2.2]
      have hle := h.length_le
      have heq := h.eq_of_length (by omega)
      rw [heq]; exact List.prefix_refl _
  imodintro
  iframe Hstate
  ipureintro
  refine ⟨?_, hf.2.1, replayDurAgrees S fp l hf.1 hf.2.1 hd⟩
  have hs : σ.ents.Sublist (fp ++ S.ents) := by
    rw [holds.2.2.1, RaftState.entsFrom]
    exact (List.drop_sublist ..).trans (List.sublist_append_right ..)
  exact (List.pairwise_map.mpr (ordered.sublist hs))
end EtcdGrove
end Perennial
