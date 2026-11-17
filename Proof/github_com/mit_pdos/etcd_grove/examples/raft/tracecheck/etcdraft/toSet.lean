/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `toSet`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.toSet
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.parseID
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem forall2_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} (_ : List.Forall₂ R l1 l2) {i : Nat} {a : α} {b : β},
      l1[i]? = some a → l2[i]? = some b → R a b
  | [], [], _, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, .cons hr hrest, 0, _, _, h1, h2 => by
    simp at h1 h2; subst h1; subst h2; exact hr
  | _ :: _, _ :: _, .cons _ hrest, i + 1, _, _, h1, h2 => by
    simp at h1 h2; exact forall2_getElem? hrest h1 h2

theorem toSet.wp_proof (wp_parseID : parseID.spec (GF := GF) (hG := hG))
    (wp_NewSet : NewSet.spec (GF := GF) (hG := hG)) :
    toSet.spec (GF := GF) (hG := hG) := by
  intro sl dq gss ids
  wp_start as ⟨Hsl, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  have Hll : gss.length = ids.length := Hrel.length_eq
  wp_auto
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List w64) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap w64 (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (sv : GoString) (osl : GoSlice) (ws : List w64),
      "i" ∷ i_ptr ↦ n ∗ "s" ∷ s_ptr ↦ sv ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* ws ∗
      "Hcap" ∷ ownSliceCap w64 osl (DFrac.own 1) ∗ "Hsl" ∷ sl ↦*{dq} gss ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (ids.take (sint.nat n)).mapM parseID = some (ws.map (fun w => uint.nat w))⌝) $$ [i s out Hnil Hcap0 Hsl]
  · iexists _, _, _, []
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < gss.length := by clear hacc; rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, gss[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, ids[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem (Hll ▸ Hlt)⟩
    have hyx : strRel y x := forall2_getElem? Hrel Hy Hx
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) gss dq y hn0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hy
    try wp_auto
    wp_apply wp_parseID y x $$ [] as %id %ok %Hid
    · ipureintro; exact hyx
    have htk : ids.take (sint.nat n + 1) = ids.take (sint.nat n) ++ [x] := by
      rw [List.take_add_one, Hx]; rfl
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
    cases hp : parseID x with
    | none =>
      rw [hp] at Hid
      subst Hid
      try wp_auto
      wp_for_post
      try wp_auto
      have : toSet ids = none := by
        unfold toSet
        conv => lhs; rw [← List.take_append_drop (sint.nat n) ids, List.drop_eq_getElem_cons (Hll ▸ Hlt)]
        rw [show ids[sint.nat n] = x from (List.getElem?_eq_some_iff.1 Hx).2]
        simp [List.mapM_append, hacc, hp]
      rw [this]
      iapply HΦ
      iframe Hsl
      ipureintro; trivial
    | some v =>
      rw [hp] at Hid
      obtain ⟨rfl, hv⟩ := Hid
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl0 ⟨Hsl0, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by clear hacc; word, by clear hacc; word, ?_⟩
      rw [hn1', htk]
      simp [List.mapM_append, hacc, hp, hv]
  · try wp_auto
    have hnx : sint.nat n = ids.length := by clear hacc; rw [← Hll, Hlen.1]; word
    rw [hnx, List.take_length] at hacc
    imod ownSlice_persist $$ Hout with #Hout
    wp_apply wp_NewSet osl ws $$ [Hout] as %st #Hst
    · iexact Hout
    try wp_auto
    have : toSet ids = some (SetIds.mk (ws.map (fun x => uint.nat x))) := by
      unfold toSet; rw [hacc]; rfl
    rw [this]
    iapply HΦ
    iframe Hsl
    isplitr
    · ipureintro; trivial
    iexact Hst

end proof

end Etcdraft
end EtcdGrove
end Perennial
