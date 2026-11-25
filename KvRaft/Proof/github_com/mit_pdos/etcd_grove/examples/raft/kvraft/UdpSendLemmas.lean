/-
# kvraft-udp's sender: the names' ghost steps (2026-11-24)

`notes/kvraft-udp-proof-plan.md`, "Ghost state". The two steps the sender takes in the names' invariant
`udpMsgInv` (`UdpDefs.lean`):

* `udp_seq_fresh` (`udpNet.nextSeq`): the process's counter `c` (below the largest word) moves to
  `c + 1`, and the name `(f, b, c + 1)`, fresh (every recorded or reserved name of the process is at
  most `c`), is reserved: its token `udpSeqTok`.
* `udp_record` (`udpTransport.runPeer`): a reserved name's token is traded for the persistent record
  of the body sent under it (`udpMsgAt`): a reserved name is not recorded, so the record is new.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

/-- **The names' facts at `nextSeq`**: with the process `(f, b)`'s counter `c` below `c + 1`, the name
`(f, b, c + 1)` is neither recorded nor reserved, and reserving it with the counter raised to `c + 1`
keeps the facts. -/
theorem udpMsgOk_seq {M : GMap MsgKey (List w8)} {T : GMap MsgKey Bool} {C : GMap (w64 × w64) w64}
    {H : GMap w64 w64} (hok : UdpMsgOk M T C H) (f b c : w64)
    (hC : C !! ((f, b) : w64 × w64) = some c) (hlt : uint.nat c < uint.nat (c + 1)) :
    T !! ((f, b, c + 1) : MsgKey) = none ∧
      UdpMsgOk M (<[((f, b, c + 1) : MsgKey) := true]> T) (<[((f, b) : w64 × w64) := c + 1]> C) H := by
  obtain ⟨h1, h2, h3⟩ := hok
  have hnew : ∀ k : MsgKey, ((M !! k).isSome ∨ (T !! k).isSome) → k ≠ (f, b, c + 1) := by
    intro k hk e
    subst e
    obtain ⟨c', hc', hle⟩ := h1 _ hk
    simp only at hc' hle
    rw [hC] at hc'
    cases hc'
    omega
  have hT : T !! ((f, b, c + 1) : MsgKey) = none := by
    cases hT : T !! ((f, b, c + 1) : MsgKey) with
    | none => rfl
    | some x => exact absurd rfl (hnew _ (Or.inr (by rw [hT]; rfl)))
  have hM : M !! ((f, b, c + 1) : MsgKey) = none := by
    cases hM : M !! ((f, b, c + 1) : MsgKey) with
    | none => rfl
    | some x => exact absurd rfl (hnew _ (Or.inl (by rw [hM]; rfl)))
  refine ⟨hT, ?_, ?_, ?_⟩
  · intro k hk
    by_cases e : ((f, b, c + 1) : MsgKey) = k
    · subst e
      exact ⟨c + 1, GMap.lookup_insert _ _ _, Nat.le_refl _⟩
    · rw [GMap.lookup_insert_ne _ _ e] at hk
      obtain ⟨c', hc', hle⟩ := h1 k hk
      by_cases e' : ((f, b) : w64 × w64) = (k.1, k.2.1)
      · rw [← e', hC] at hc'
        cases hc'
        refine ⟨c + 1, ?_, by omega⟩
        rw [← e']
        exact GMap.lookup_insert _ _ _
      · exact ⟨c', by rw [GMap.lookup_insert_ne _ _ e']; exact hc', hle⟩
  · intro k hk
    by_cases e : ((f, b, c + 1) : MsgKey) = k
    · subst e; exact hM
    · rw [GMap.lookup_insert_ne _ _ e] at hk
      exact h2 k hk
  · intro fb c' hc'
    by_cases e : ((f, b) : w64 × w64) = fb
    · subst e
      exact h3 _ c hC
    · rw [GMap.lookup_insert_ne _ _ e] at hc'
      exact h3 fb c' hc'

/-- **The names' facts at the record**: a reserved name, recorded with the body `body` and its
reservation dropped, keeps the facts; it was not recorded. -/
theorem udpMsgOk_record {M : GMap MsgKey (List w8)} {T : GMap MsgKey Bool} {C : GMap (w64 × w64) w64}
    {H : GMap w64 w64} (hok : UdpMsgOk M T C H) (k : MsgKey) (hT : T !! k = some true)
    (body : List w8) :
    M !! k = none ∧ UdpMsgOk (<[k := body]> M) (T.delete k) C H := by
  obtain ⟨h1, h2, h3⟩ := hok
  have hM : M !! k = none := h2 k (by rw [hT]; rfl)
  refine ⟨hM, ?_, ?_, h3⟩
  · intro k' hk'
    by_cases e : k = k'
    · subst e
      exact h1 k (Or.inr (by rw [hT]; rfl))
    · rw [GMap.lookup_insert_ne _ _ e, GMap.lookup_delete_ne _ e] at hk'
      exact h1 k' hk'
  · intro k' hk'
    by_cases e : k = k'
    · subst e
      rw [GMap.lookup_delete] at hk'
      cases hk'
    · rw [GMap.lookup_delete_ne _ e] at hk'
      rw [GMap.lookup_insert_ne _ _ e]
      exact h2 k' hk'

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]

/-- **`nextSeq`'s ghost step** (see the file header). -/
theorem udp_seq_fresh (γu : UdpNames) (f b c : w64) (hlt : uint.nat c < uint.nat (c + 1))
    (E : CoPset) (hE : ↑udpMsgN ⊆ E) :
    ⊢ udpMsgInv (GF := GF) γu -∗ udpCtr γu f b c ={E}=∗
      udpCtr γu f b (c + 1) ∗ udpSeqTok γu (f, b, c + 1) := by
  iintro #Hinv Hc
  unfold udpMsgInv
  imod inv_acc hE $$ Hinv with ⟨Hb, Hclose⟩
  imod Hb with ⟨%M, %T, %C, %H, HM, HT, HC, HH, %hok⟩
  unfold udpCtr
  ihave %hC := ghost_map_lookup $$ HC Hc
  obtain ⟨hT, hok'⟩ := udpMsgOk_seq hok f b c hC hlt
  imod ghost_map_update (c + 1) $$ HC Hc with ⟨HC, Hc⟩
  imod ghost_map_insert ((f, b, c + 1) : MsgKey) true hT $$ HT with ⟨HT, Ht⟩
  imod Hclose $$ [HM HT HC HH] with -
  · inext
    iexists M, _, _, H
    iframe HM HT HC HH
    ipureintro
    exact hok'
  imodintro
  unfold udpSeqTok
  iframe Hc Ht

/-- **The record step** (see the file header). -/
theorem udp_record (γu : UdpNames) (k : MsgKey) (body : List w8) (E : CoPset) (hE : ↑udpMsgN ⊆ E) :
    ⊢ udpMsgInv (GF := GF) γu -∗ udpSeqTok γu k ={E}=∗ udpMsgAt γu k body := by
  iintro #Hinv Ht
  unfold udpMsgInv
  imod inv_acc hE $$ Hinv with ⟨Hb, Hclose⟩
  imod Hb with ⟨%M, %T, %C, %H, HM, HT, HC, HH, %hok⟩
  unfold udpSeqTok
  ihave %hT := ghost_map_lookup $$ HT Ht
  obtain ⟨hM, hok'⟩ := udpMsgOk_record hok k hT body
  imod ghost_map_delete $$ HT Ht with HT
  imod ghost_map_insert_persist k body hM $$ HM with ⟨HM, #Hm⟩
  imod Hclose $$ [HM HT HC HH] with -
  · inext
    iexists _, _, C, H
    iframe HM HT HC HH
    ipureintro
    exact hok'
  imodintro
  unfold udpMsgAt
  iexact Hm

end ghost

end kvraft
end EtcdGrove
end Perennial
