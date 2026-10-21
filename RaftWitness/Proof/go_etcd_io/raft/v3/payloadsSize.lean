/-
Port of election_proof/proof_payloadsSize.v.
-/
module

public import Spec.go_etcd_io.raft.v3.payloadsSize
public import Spec.go_etcd_io.raft.v3.payloadSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `entsSize`'s loop. The accumulator is existential, with one
implication in the invariant: *if* every payload is empty it is still
`0`. (It used to be pinned to `0` under a `Forall` premise on the
lemma; widened 2026-09-20 for `maybeSendAppend`, which weighs entries
that came out of the log.) `ent` is allocated outside the loop and
written on every iteration, so it too is existentially quantified
(`notes/gotchas.md`, "A `for … range` loop variable must be inside the
`wp_for` invariant"). -/
theorem payloadsSize.wp_proof
    (wp_payloadSize : payloadSize.spec (GF := GF) (hG := hG)) :
    payloadsSize.spec (GF := GF) (hG := hG) := by
  intro s es dq
  wp_start as H
  iNamed H
  iunfold entsPts at Hs
  icases Hs with ⟨%ls, Hs, #Hb⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  ihave IH : iprop(∃ (n acc : w64) (ev : Loc),
      "i" ∷ i_ptr ↦ n ∗
      "size" ∷ s_ptr ↦ acc ∗
      "ent" ∷ e_ptr ↦ ev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (es.length : Int)⌝ ∗
      "%Hacc" ∷ ⌜(∀ e ∈ es, e.Data' = []) → acc = W64 0⌝) $$ [i s e]
  · iexists _, _, _
    iframe
    ipureintro
    exact ⟨⟨by word, by word⟩, fun _ => rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < es.length := by word
    obtain ⟨e, He⟩ : ∃ e, es[(sint.Z n).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases entsBig_lookup ls es _ e He $$ Hb with ⟨%l, %Hl, #Hl⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index s (sint.Z n) ls dq l Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hl
    wp_apply wp_payloadSize l DFrac.discard e $$ [$Hl] as -
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    -- if every payload is empty then so is this one, and the accumulator
    -- was `0` by the invariant
    intro Hzero
    have Hz0 := Hzero e (List.mem_of_getElem? He)
    rw [Hacc Hzero, Hz0, List.length_nil]
    word
  · iapply HΦ
    isplitl
    · iunfold entsPts
      iexists ls
      iframe Hs Hb
    ipureintro; exact Hacc

end proof

end EtcdGrove
end Perennial
