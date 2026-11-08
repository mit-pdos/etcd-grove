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
  intro r s dq es tl
  wp_start as ⟨Hs, #Htl, %Hok⟩
  iunfold entsPts at Hs
  icases Hs with ⟨%ls, Hs, #Hb⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  rename_i k_ptr
  ihave IH : iprop(∃ (n k : w64),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ k ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (es.length : Int)⌝) $$ [-HΦ Hs es r]
  · iexists _, _
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
    wp_apply wp_Entry_GetType.1 l DFrac.discard e $$ [$Hl] as -
    wp_if_destruct
    · wp_apply wp_traceNodeEvent $$ [$Htl]
      · ipureintro; exact Hok
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
  · iapply HΦ
    iunfold entsPts
    iexists ls
    iframe Hs Hb

end proof

end EtcdGrove
end Perennial
