module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.viewFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histLen

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state hview)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem viewFrom_ge (n lo1 : w64) (len : Nat) (hn : uint.Z n = len) (h : ¬ uint.Z n < uint.Z lo1) :
    uint.nat lo1 ≤ len := by
  have h2 : uint.Z lo1 = (uint.nat lo1 : Int) := by word
  rw [hn, h2] at h; omega

theorem viewFrom_nat (n : w64) (k : Nat) (hn : n = W64 (k : Int)) (hk : k < 2 ^ 63) :
    uint.nat n = k := by
  subst hn; word

theorem viewFrom_exit (lp i : Nat) (lo1 n : w64) (hnl : uint.nat n = lp + 1)
    (hgo : ¬ uint.Z lo1 ≤ uint.Z n) (hle : uint.nat lo1 + i ≤ lp + 1) : False := by
  have : uint.nat n < uint.nat lo1 := by word
  omega

theorem viewFrom_le (lp : Nat) (lo1 n : w64) (hnl : uint.nat n = lp + 1)
    (hgo : uint.Z lo1 ≤ uint.Z n) : uint.nat lo1 ≤ lp + 1 := by
  have : uint.nat lo1 ≤ uint.nat n := by word
  omega

theorem viewFrom_idx (len lp sslen : Nat) (lo1 n : w64) (sllen : w64) (hlt : len < 2 ^ 63)
    (hpl : lp + 1 ≤ len) (hnl : uint.nat n = lp + 1) (hgo : uint.Z lo1 ≤ uint.Z n)
    (hss : sslen = len - uint.nat lo1 + 1) (hsll : sslen = sint.nat sllen ∧ 0 ≤ sint.Z sllen) :
    lp + 1 - uint.nat lo1 < sslen ∧ sint.nat (n - lo1) = lp + 1 - uint.nat lo1 ∧
      0 ≤ sint.Z (n - lo1) ∧ sint.Z (n - lo1) < sint.Z sllen := by
  have h1 : uint.nat lo1 ≤ uint.nat n := by word
  have h2 : uint.nat (n - lo1) = uint.nat n - uint.nat lo1 := by word
  refine ⟨by omega, ?_, ?_, ?_⟩
  · word
  · word
  · have : (sslen : Int) = sint.Z sllen := by rw [hsll.1]; word
    word

theorem viewFrom.wp_proof
    (wp_histLen : histLen.spec (GF := GF) (hG := hG)) :
    viewFrom.spec (GF := GF) (hG := hG) := by
  intro h hs lo Hlt
  unfold hviewOwn
  wp_start as #Hh
  wp_auto
  wp_apply wp_max_u64 as %lo1 %Hlo1
  (try wp_auto)
  wp_apply wp_histLen $$ [$Hh]
  (try wp_auto)
  have hn : uint.Z (W64 (hs.length : Int)) = hs.length := by word
  have hlo1 : 1 ≤ uint.nat lo1 := by
    have : uint.nat (W64 1) = 1 := rfl
    rw [Hlo1]; omega
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    isplit
    · iexact Hh
    iexists []
    isplit
    · iapply ownSlice_nil
    · iintro !> %i %s %H
      simp at H
  · have hge : uint.nat lo1 ≤ hs.length := by
      exact viewFrom_ge _ _ _ hn Hif
    wp_apply wp_slice_make2 as %sl ⟨Hsl, -⟩
    · ipureintro; word
    (try wp_auto)
    have hsz0 : uint.Z (W64 (hs.length : Int) - lo1 + W64 1) = hs.length - uint.nat lo1 + 1 := by
      word
    have hsz : sint.nat (W64 (hs.length : Int) - lo1 + W64 1) = hs.length - uint.nat lo1 + 1 := by
      have := hsz0; word
    ihave HI : (∃ (cur : Loc) (l : List GSt) (ss : List mstore), "x" ∷ x_ptr ↦ cur ∗ "Hsl" ∷ sl ↦* ss ∗
        "#Hc" ∷ histOwn cur l ∗ "%Hp" ∷ ⌜l <+: hs ∧ ss.length = hs.length - uint.nat lo1 + 1⌝ ∗
        "#Hcell" ∷ □ (∀ (i : Nat) (s : mstore), ⌜ss[i]? = some s⌝ -∗
          (⌜uint.nat lo1 + i ≤ l.length⌝ ∨ storeOwn s (histN hs (uint.nat lo1 + i)))) : IProp GF) $$ [x Hsl]
    · iexists h, hs, _
      iframe
      isplit
      · iexact Hh
      isplit
      · ipureintro; refine ⟨List.prefix_refl _, ?_⟩; rw [List.length_replicate]; exact hsz
      · iintro !> %i %s %H
        ileft; ipureintro
        have := (List.getElem?_eq_some_iff.1 H).1
        rw [List.length_replicate, hsz] at this; omega
    wp_for HI
    rcases List.eq_nil_or_concat l with rfl | ⟨l', s0, he⟩
    · icases (histOwn_nil cur).1 $$ Hc with %Hn
      subst Hn
      imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
      wp_if_destruct
      · (try wp_auto)
        iapply HΦ
        isplit
        · iexact Hh
        iexists ss
        isplit
        · iexact Hsl
        iintro !> %i %s %H
        icases Hcell $$ %i %s %H with (%Hle | Hst)
        · iexfalso; ipureintro; simp at Hle; omega
        · iexact Hst
      · exact absurd rfl Hif
    · rw [List.concat_eq_append] at he; subst he
      icases (histOwn_snoc cur l' s0).1 $$ Hc with ⟨%hn0, #Hp, #Hs, %Hn, #Hr⟩
      icases (typedPointsto_not_null _ _ _) $$ Hp with %Hnn
      wp_if_destruct
      · exact absurd rfl Hnn
      iStructNamed Hp
      have hpl : l'.length + 1 ≤ hs.length := by
        have := Hp.1.length_le; simpa using this
      have hnl : uint.nat hn0.n' = l'.length + 1 := viewFrom_nat _ _ Hn (by omega)
      by_cases hgo : uint.Z lo1 ≤ uint.Z hn0.n'
      · wp_auto
        wp_if_destruct
        · ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
          obtain ⟨hi0, hidx, hb0, hb1⟩ := viewFrom_idx _ _ _ _ _ _ Hlt hpl hnl hgo Hp.2 Hsll
          list_elem ss (l'.length + 1 - uint.nat lo1) as old
          have hb : 0 ≤ sint.Z (hn0.n' - lo1) ∧ sint.Z (hn0.n' - lo1) < sint.Z sl.len := ⟨hb0, hb1⟩
          icases ownSlice_elem_acc (sint.Z (hn0.n' - lo1)) old sl _ ss hb.1
            (by rw [← hidx] at Hold_lookup; simpa [sint.nat] using Hold_lookup) $$ Hsl with ⟨He, Hsl⟩
          iterate 3 ((try simp only [hb, _root_.and_self, ↓reduceIte]); (try wp_auto))
          ispecialize Hsl $$ %hn0.st' He
          have hset : (sint.Z (hn0.n' - lo1)).toNat = l'.length + 1 - uint.nat lo1 := hidx
          rw [hset]
          have hs0 : histN hs (l'.length + 1) = s0 := histN_prefix _ _ _ Hp.1
          wp_for_post
          iframe
          iexists hn0.prev', l', ss.set (l'.length + 1 - uint.nat lo1) hn0.st'
          isplitl [x]
          · iexact x
          isplitl [Hsl]
          · iexact Hsl
          isplit
          · iexact Hr
          isplit
          · ipureintro
            refine ⟨(List.prefix_append _ _).trans Hp.1, ?_⟩
            rw [List.length_set]; exact Hp.2
          · iintro !> %i %s %H
            by_cases hi : i = l'.length + 1 - uint.nat lo1
            · subst hi
              rw [List.getElem?_set_self hi0] at H
              cases H
              iright
              have : uint.nat lo1 + (l'.length + 1 - uint.nat lo1) = l'.length + 1 := by
                have := viewFrom_le _ _ _ hnl hgo; omega
              rw [this, hs0]
              iexact Hs
            · rw [List.getElem?_set_ne (Ne.symm hi)] at H
              icases Hcell $$ %i %s %H with (%Hle | Hst)
              · ileft; ipureintro
                simp only [List.length_append, List.length_singleton] at Hle
                have := viewFrom_le _ _ _ hnl hgo
                omega
              · iright; iexact Hst
        · exact absurd (by rw [decide_eq_true hgo]) Hif
      · imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
        wp_auto
        have hft : (#false : val) ≠ #true := fun h => by
          have := GoGlobalContext.intoVal_inj_bool h; simp at this
        rw [decide_eq_false hgo, decide_eq_false hft]
        simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        simp only [decide_true, ↓reduceIte]
        (try wp_auto)
        iapply HΦ
        isplit
        · iexact Hh
        iexists ss
        isplit
        · iexact Hsl
        iintro !> %i %s %H
        icases Hcell $$ %i %s %H with (%Hle | Hst)
        · iexfalso; ipureintro
          simp only [List.length_append, List.length_singleton] at Hle
          exact viewFrom_exit _ _ _ _ hnl hgo Hle
        · iexact Hst

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
