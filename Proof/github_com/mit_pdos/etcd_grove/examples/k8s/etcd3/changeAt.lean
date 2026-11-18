module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.changeAt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem changeAtL_drop_cons_nil (ps : List item) (i : Nat) (r : Nat) (p : item)
    (hp : ps[i]? = some p) :
    changeAtL (ps.drop i) [] r = some ⟨p.key', some p.obj', none, r⟩ := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hp).1,
    (List.getElem?_eq_some_iff.1 hp).2]
  rfl

theorem changeAtL_nil_drop_cons (qs : List item) (j : Nat) (r : Nat) (q : item)
    (hq : qs[j]? = some q) :
    changeAtL [] (qs.drop j) r = some ⟨q.key', none, some q.obj', r⟩ := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hq).1,
    (List.getElem?_eq_some_iff.1 hq).2]
  rfl

theorem changeAtL_drop_cons (ps qs : List item) (i : Nat) (r : Nat) (p q : item)
    (hp : ps[i]? = some p) (hq : qs[i]? = some q) :
    changeAtL (ps.drop i) (qs.drop i) r =
      if decide (go.GoStringLt p.key' q.key') then some ⟨p.key', some p.obj', none, r⟩
      else if decide (go.GoStringLt q.key' p.key') then some ⟨q.key', none, some q.obj', r⟩
      else if decide (p = q) then changeAtL (ps.drop (i + 1)) (qs.drop (i + 1)) r
      else some ⟨p.key', some p.obj', some q.obj', r⟩ := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hp).1,
    (List.getElem?_eq_some_iff.1 hp).2,
    List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hq).1,
    (List.getElem?_eq_some_iff.1 hq).2]
  rfl

theorem item_eq_iff3 (a b : item) :
    a = b ↔ a.key' = b.key' ∧ a.obj' = b.obj' ∧ a.canon' = b.canon' := by
  obtain ⟨_, _, _⟩ := a
  obtain ⟨_, _, _⟩ := b
  simp

theorem changeAt.wp_proof : changeAt.spec (GF := GF) (hG := hG) := by
  intro p c gp gc r
  wp_start as ⟨#Hp, #Hc⟩
  unfold storeOwn
  icases Hp with ⟨#Hpk, %Hprv⟩
  icases Hc with ⟨#Hck, %Hcrv⟩
  ihave %Hlp := ownSlice_len $$ Hpk
  ihave %Hlc := ownSlice_len $$ Hck
  wp_auto
  ihave HI : (∃ (k : w64),
      "i" ∷ i_ptr ↦ k ∗ "j" ∷ j_ptr ↦ k ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ gp.items.length ∧ sint.nat k ≤ gc.items.length ∧
        changeAtL gp.items gc.items (uint.nat r) =
          changeAtL (gp.items.drop (sint.nat k)) (gc.items.drop (sint.nat k)) (uint.nat r)⌝ : IProp GF)
      $$ [i j]
  · iexists W64 0
    iframe
    ipureintro; refine ⟨by word, by word, by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have hkp := Hif; clear Hif
    list_elem gp.items (sint.nat k) as pi
    wp_if_destruct
    · have hkc := Hif; clear Hif
      have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z p.items'.len := ⟨Hk.1, hkp⟩
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index p.items' (sint.Z k) gp.items _ pi Hk.1 $$ [Hpk] as -
      · isplit
        · iexact Hpk
        · ipureintro; exact Hpi_lookup
      wp_for_post
      iapply HΦ
      ipureintro
      have hdc : gc.items.drop (sint.nat k) = [] := List.drop_eq_nil_of_le (by word)
      rw [Hk.2.2.2, hdc, changeAtL_drop_cons_nil _ _ _ pi Hpi_lookup]
      simp [chgOf]
    · have hkc := Hif; clear Hif
      list_elem gc.items (sint.nat k) as ci
      have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z p.items'.len := ⟨Hk.1, hkp⟩
      have hb2 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z c.items'.len := ⟨Hk.1, by word⟩
      icases ownSlice_elem_acc (sint.Z k) pi p.items' _ gp.items Hk.1 (by simpa [sint.nat] using Hpi_lookup)
        $$ Hpk with ⟨#Hpe, -⟩
      icases ownSlice_elem_acc (sint.Z k) ci c.items' _ gc.items Hk.1 (by simpa [sint.nat] using Hci_lookup)
        $$ Hck with ⟨#Hce, -⟩
      iStructNamedSuffix Hpe "_p"
      iStructNamedSuffix Hce "_c"
      wp_if_destruct
      · iterate 3 ((try simp only [hb, hb2, _root_.and_self, ↓reduceIte]); (try wp_auto))
        have hcons := changeAtL_drop_cons gp.items gc.items (sint.nat k) (uint.nat r) pi ci
          Hpi_lookup Hci_lookup
        wp_if_destruct
        · have hlt : go.GoStringLt pi.key' ci.key' := by simpa using Hif
          iterate 3 ((try simp only [hb, hb2, _root_.and_self, ↓reduceIte]); (try wp_auto))
          wp_for_post
          iapply HΦ
          ipureintro
          rw [Hk.2.2.2, hcons]
          simp [hlt, chgOf]
        · have hlt : ¬ go.GoStringLt pi.key' ci.key' := by simpa using Hif
          clear Hif
          iterate 3 ((try simp only [hb, hb2, _root_.and_self, ↓reduceIte]); (try wp_auto))
          wp_if_destruct
          · exfalso; word
          iterate 3 ((try simp only [hb, hb2, _root_.and_self, ↓reduceIte]); (try wp_auto))
          wp_if_destruct
          · have hlt2 : go.GoStringLt ci.key' pi.key' := by simpa using Hif
            iterate 3 ((try simp only [hb, hb2, _root_.and_self, ↓reduceIte]); (try wp_auto))
            wp_for_post
            iapply HΦ
            ipureintro
            rw [Hk.2.2.2, hcons]
            simp [hlt, hlt2, chgOf]
          · have hlt2 : ¬ go.GoStringLt ci.key' pi.key' := by simpa using Hif
            clear Hif
            iterate 3 ((try simp only [hb, hb2, _root_.and_self, ↓reduceIte]); (try wp_auto))
            repeat' wp_if_destruct
            all_goals first
              | (have hpq : pi = ci := by
                   rw [item_eq_iff3, Obj_eq_iff]; and_intros <;> assumption
                 wp_for_post
                 iframe
                 iexists k + W64 1
                 iframe
                 ipureintro
                 have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
                 have hlp := (List.getElem?_eq_some_iff.1 Hpi_lookup).1
                 have hlc := (List.getElem?_eq_some_iff.1 Hci_lookup).1
                 refine ⟨by word, by rw [hk1]; omega, by rw [hk1]; omega, ?_⟩
                 rw [hk1, Hk.2.2.2, hcons]
                 simp only [decide_eq_false hlt, decide_eq_false hlt2, decide_eq_true hpq,
                   Bool.false_eq_true, ↓reduceIte])
              | (have hpq : pi ≠ ci := fun h => by
                   rw [item_eq_iff3, Obj_eq_iff] at h; simp_all
                 wp_for_post
                 iapply HΦ
                 ipureintro
                 rw [Hk.2.2.2, hcons]
                 simp [hlt, hlt2, hpq, chgOf])
      · exact absurd hkp Hif
  · have hkp := Hif; clear Hif
    wp_if_destruct
    · have hkc := Hif; clear Hif
      list_elem gc.items (sint.nat k) as ci
      have hb2 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z c.items'.len := ⟨Hk.1, hkc⟩
      iterate 3 ((try simp only [hb2, _root_.and_self, ↓reduceIte]); (try wp_auto))
      repeat' wp_if_destruct
      all_goals first
        | (exfalso; word)
        | (simp only [hb2, _root_.and_self, ↓reduceIte]
           wp_apply wp_load_slice_index c.items' (sint.Z k) gc.items _ ci Hk.1 $$ [Hck] as -
           · isplit
             · iexact Hck
             · ipureintro; exact Hci_lookup
           wp_for_post
           iapply HΦ
           ipureintro
           have hdp : gp.items.drop (sint.nat k) = [] := List.drop_eq_nil_of_le (by word)
           rw [Hk.2.2.2, hdp, changeAtL_nil_drop_cons _ _ _ ci Hci_lookup]
           simp [chgOf])
    · iapply HΦ
      ipureintro
      have hdp : gp.items.drop (sint.nat k) = [] := List.drop_eq_nil_of_le (by word)
      have hdc : gc.items.drop (sint.nat k) = [] := List.drop_eq_nil_of_le (by word)
      rw [Hk.2.2.2, hdp, hdc]
      rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
