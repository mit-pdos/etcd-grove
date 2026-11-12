/-
Port of election_proof/proof_traceReplicate.v.
-/
module

public import Spec.go_etcd_io.raft.v3.traceReplicate
public import Spec.go_etcd_io.raft.v3.traceNodeEvent
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceReplicate.wp_proof
    (wp_traceNodeEvent : traceNodeEvent.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG)) :
    traceReplicate.spec (GF := GF) (hG := hG) := by
  intro c r id st s dq es tl Q
  wp_start as ⟨Hs, #Htl, Hown, Hfire⟩
  iunfold entsPts at Hs
  icases Hs with ⟨%ls, Hs, #Hb⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  rename_i k_ptr
  ihave IH : iprop(∃ (n k : w64),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ k ∗
      "Hown" ∷ trOwn st.gh.tr (ownRaftPhysCV c c.voters r id st) ∗
      "Hfire" ∷ TraceFireN st.gh.tr tl (NodeEvOf (W64 5) id st c) (normalCount (es.drop (sint.Z n).toNat)) Q ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (es.length : Int)⌝) $$ [-HΦ Hs es r]
  · iexists _, (W64 0)
    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.drop_zero]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < es.length := by word
    obtain ⟨e, He⟩ : ∃ e, es[(sint.Z n).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases entsBig_lookup ls es _ e He $$ Hb with ⟨%l, %Hl, #Hl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index s (sint.Z n) ls dq l Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index s (sint.Z n) ls dq l Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hl
    have Hdrop : es.drop (sint.Z n).toNat = e :: es.drop (sint.Z (n + W64 1)).toNat := by
      rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, List.drop_eq_getElem_cons Hlt]
      congr 1
      exact Option.some_inj.mp ((List.getElem?_eq_getElem Hlt).symm.trans He)
    rw [Hdrop]
    wp_apply wp_Entry_GetType.1 l DFrac.discard e $$ [$Hl] as -
    wp_if_destruct
    · have hN : decide (e.Type' = EntryNormal) = true :=
        decide_eq_true (by rw [Hif]; rfl)
      rw [show normalCount (e :: es.drop (sint.Z (n + W64 1)).toNat) =
          normalCount (es.drop (sint.Z (n + W64 1)).toNat) + 1 by
        simp only [normalCount, List.filter_cons, hN, if_true, List.length_cons]]
      simp only [TraceFireN]
      ihave Hown := trOwn_physLend _ c r id st $$ Hown
      wp_apply wp_traceNodeEvent (W64 5) c r id st tl _ _ (by decide) $$ [$Htl $Hown $Hfire]
        as ⟨Hown, Hfire⟩
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    · have hN : decide (e.Type' = EntryNormal) = false :=
        decide_eq_false (fun h => Hif (by rw [h]; rfl))
      rw [show normalCount (e :: es.drop (sint.Z (n + W64 1)).toNat) =
          normalCount (es.drop (sint.Z (n + W64 1)).toNat) by
        simp only [normalCount, List.filter_cons, hN, Bool.false_eq_true, if_false]]
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
  · rw [List.drop_eq_nil_of_le (by word)] at *
    iapply HΦ
    iframe Hown
    isplitr [Hfire]
    · iunfold entsPts
      iexists ls
      iframe Hs Hb
    simp only [normalCount, List.filter_nil, List.length_nil, TraceFireN, TraceFireOpt]
    iexact Hfire

end proof

end EtcdGrove
end Perennial
