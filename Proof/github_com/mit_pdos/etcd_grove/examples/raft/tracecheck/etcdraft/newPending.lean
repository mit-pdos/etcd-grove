/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `newPending`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.newPending
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Domain
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.oneMoreMessage

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

theorem newPending.wp_proof (wp_Domain : Bag.Domain.spec (GF := GF) (hG := hG))
    (wp_oneMoreMessage : oneMoreMessage.spec (GF := GF) (hG := hG)) :
    newPending.spec (GF := GF) (hG := hG) := by
  intro p s p2 s2 f P
  wp_start as ⟨#Hs, #Hs2, #Hf⟩
  ihave #Hs20 := Hs2
  iunfold stateRO at Hs20
  icases Hs20 with ⟨%g2, %sm2, #Hp2, -, -, -, -, -, -, #Hpm2, -⟩
  icases typedPointsto_split _ _ _ $$ Hp2 with Hpf2
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf2 with ⟨-, -, -, #PM2, -⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Domain_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Domain g2.PendingMessages' s2.pendingMessages $$ [Hpm2] as %sl #Hsl
  · iexact Hpm2
  iunfold msgsRO at Hsl
  icases Hsl with ⟨%ps, #Hps, #Hpl⟩
  ihave %Hlen := ownSlice_len $$ Hps
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hpl
  obtain ⟨F, hF⟩ : ∃ F : Msg → Bool, F = fun m => P m && oneMoreMessage s s2 m := ⟨_, rfl⟩
  ihave IH : iprop(∃ (n : w64) (x : Loc),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (s2.pendingMessages.domain.take (sint.nat n)).any F = false⌝) $$ [i m]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hna⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by clear hna; rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, ps[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, s2.pendingMessages.domain[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Hll ▸ Hlt)⟩
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => msgRO (GF := GF) a b) Hy Hx $$ Hpl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) ps DFrac.discard y hn0 $$ [Hps] as -
    · isplitr
      · iexact Hps
      ipureintro; exact Hy
    try wp_auto
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hna; word
    have htake : (s2.pendingMessages.domain.take (sint.nat n + 1)).any F =
        ((s2.pendingMessages.domain.take (sint.nat n)).any F || F x) := by
      rw [List.take_add_one, Hx]; simp
    ihave #Hfy := Hf $$ %y %x
    wp_apply Hfy $$ [Hyx]
    · iexact Hyx
    cases hP : P x
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hna htake; word, by clear hna htake; word, ?_⟩
      rw [hn1', htake, hna]; simp [hF, hP]
    try wp_auto
    wp_apply wp_oneMoreMessage p s p2 s2 y x $$ [Hs Hs2 Hyx]
    · iframe Hs Hs2 Hyx
    cases ho : oneMoreMessage s s2 x
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hna htake; word, by clear hna htake; word, ?_⟩
      rw [hn1', htake, hna]; simp [hF, hP, ho]
    · try wp_auto
      wp_for_post
      try wp_auto
      have : newPending s s2 P = true := by
        unfold newPending
        rw [List.any_eq_true]
        exact ⟨x, List.mem_of_getElem? Hx, by simp [hP, ho]⟩
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have hnx : sint.nat n = s2.pendingMessages.domain.length := by clear hna; rw [← Hll, Hlen.1]; word
    rw [hnx, List.take_length] at hna
    have : newPending s s2 P = false := by rw [hF] at hna; exact hna
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
