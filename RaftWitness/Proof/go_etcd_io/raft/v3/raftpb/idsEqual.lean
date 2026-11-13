/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/idsEqual.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.idsEqual

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.idsEqual.wp_proof : raftpb.idsEqual.spec (GF := GF) (hG := hG) := by
  intro a b dq1 dq2 xs ys
  wp_start as ⟨Ha, Hb⟩
  ihave %Hla := ownSlice_len _ _ _ $$ Ha
  ihave %Hlb := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · -- equal lengths: the loop
    have Hlen : a.len = b.len := Hif
    rename_i igo
    irename : (igo ↦ zero_val w64 : IProp GF) => Higo
    have Hl : xs.length = ys.length := by
      rw [Hla.1, Hlb.1, Hif]
    ihave IH : iprop(∃ (n k : w64),
        "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧
          xs.take (sint.nat n) = ys.take (sint.nat n)⌝) $$ [i Higo]
    · iexists W64 0, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.take_zero]
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < xs.length := by word
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z a.len := ⟨Hn.1, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨y, Hy⟩ : ∃ y, ys[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem (Hl ▸ Hlt)⟩
      wp_apply wp_load_slice_index a (sint.Z n) _ dq1 x Hn.1 $$ [Ha] as Ha
      · iframe; ipureintro; exact Hx
      have Hbnda : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z a.len := Hbnd
      have Hbndb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z b.len := by rw [← Hlen]; exact Hbnd
      simp only [Hbnda, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index a (sint.Z n) _ dq1 x Hn.1 $$ [Ha] as Ha
      · iframe; ipureintro; exact Hx
      simp only [Hbndb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index b (sint.Z n) _ dq2 y Hn.1 $$ [Hb] as Hb
      · iframe; ipureintro; exact Hy
      wp_if_destruct
      · -- equal elements: on to the next
        wp_for_post
        iframe
        iexists n + W64 1, n
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word,
          List.take_add_one, List.take_add_one, Hn.2.2, Hx, Hy, Hif]
      · -- a mismatch: false
        wp_for_post
        iapply HΦ
        iframe
        ipureintro
        constructor
        · intro h; exact absurd h (by decide)
        · intro h; subst h; rw [Hx] at Hy; cases Hy; exact absurd rfl Hif
    · -- the loop is done: equal
      have Hn' : sint.nat n = xs.length := by word
      iapply HΦ
      iframe
      ipureintro
      have h := Hn.2.2
      rw [Hn', List.take_length, Hl, List.take_length] at h
      exact ⟨fun _ => h, fun _ => rfl⟩
  · -- different lengths
    iapply HΦ
    iframe
    ipureintro
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; subst h; exact absurd (by rw [Hla.1] at Hlb; word) Hif

end proof

end EtcdGrove
end Perennial
