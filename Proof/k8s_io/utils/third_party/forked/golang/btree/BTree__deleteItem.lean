module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__deleteItem
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__minItems
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__mutableFor
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__remove
public import Spec.k8s_io.utils.third_party.forked.golang.btree.copyOnWriteContext__freeNode
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Remove

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree
open RemoveLemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem BTree.deleteItem.wp_proof
    (wp_minItems : BTree.minItems.spec (GF := GF) (hG := hG))
    (wp_mutableFor : node.mutableFor.spec (GF := GF) (hG := hG))
    (wp_remove : node.remove.spec (GF := GF) (hG := hG))
    (wp_freeNode : copyOnWriteContext.freeNode.spec (GF := GF) (hG := hG)) :
    BTree.deleteItem.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t s item tgt typ Htyp
  wp_start as ⟨Ht, #Hitem⟩
  unfold ownBTree
  icases Ht with ⟨%tv, %f, %less, %d, Ht, #Hcow, %Hdeg, %Hlen, %Hsorted, #Hitems, Hroot⟩
  wp_alloc_anon
  wp_pures
  wp_alloc_anon
  wp_auto
  unfold ownRoot
  icases Hroot with (%Hnil | ⟨%h, %tr, ⟨%Hsh, %Hrb, %Hel⟩, Hn⟩)
  · obtain ⟨Hr, rfl⟩ := Hnil
    rw [Hr]
    wp_auto
    simp only [removeOp_nil, Option.getD_none, Option.isSome_none]
    rw [show zero_val Bool = false from rfl]
    iapply HΦ
    iexists tv, f, less, d
    iframe Ht Hcow Hitems
    iframe %Hdeg %Hlen %Hsorted
    ileft
    ipureintro; exact ⟨Hr, by simp⟩
  · ihave %Hnn := ownNode_ne_null o tv.cow' f less _ _ tr $$ Hn
    rw [decide_eq_false Hnn]
    wp_auto
    icases ownNode_len_acc' o tv.cow' f less _ _ tr $$ Hn with ⟨%risl, %dq', Hri, ⟨%Hril, %Hril0⟩, Hrclose⟩
    wp_auto
    ihave Hn := Hrclose $$ Hri
    wp_if_destruct
    · -- an empty root
      have hi0 : tr.items = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hril, Hif]; rfl
      have hh0 : h = 0 := by
        rcases Nat.eq_zero_or_pos h with hh | hh
        · exact hh
        · have := Hrb.2 hh; rw [hi0] at this; simp at this
      subst hh0
      cases tr with
      | node is cs =>
      simp only [Tree.items_node] at hi0
      subst hi0
      rw [shape_zero] at Hsh
      subst Hsh
      simp at Hel
      subst Hel
      simp only [removeOp_nil, Option.getD_none, Option.isSome_none]
      rw [show zero_val Bool = false from rfl]
      iapply HΦ
      iexists tv, f, less, d
      iframe Ht Hcow Hitems
      iframe %Hdeg %Hlen %Hsorted
      iright
      iexists 0, Tree.node [] []
      iframe
      ipureintro; exact ⟨by rw [shape_zero], Hrb, by simp⟩
    · have h1 : 1 ≤ tr.items.length := by
        rw [Hril]
        have h2 : sint.nat risl.len ≠ 0 := by intro h0; apply Hif; word
        omega
      wp_apply wp_mutableFor o tv.cow' f less tv.root' tr $$ [Hn] as %r' Hn
      · iframe # ∗
      wp_apply wp_minItems t (DFrac.own 1) _ $$ [Ht] as Ht
      · iexact Ht
      wp_auto
      wp_apply wp_remove (T := T) o tv.cow' f less r' tr item tgt (tv.degree' - W64 1) typ d h Hsh
          (Hel ▸ Hsorted) Hrb.1 (by word) Hdeg.2.1 Hdeg.2.2 Htyp (fun _ _ => h1)
          (fun _ => .inl h1) $$ [Hn] as %out %fnd ⟨%t', Hn, %Hpost⟩
      · rw [Hel]; iframe # ∗
      rw [Hel] at Hpost
      cases t' with
      | node is' cs' =>
      obtain ⟨hs', he', hout, hfnd, hl1, hl2, -⟩ := Hpost
      icases ownedNode_open o tv.cow' f less _ r' is' cs' $$ Hn with ⟨%ps', %isl', %csl', Hr⟩
      unfold ownedRes
      icases Hr with ⟨%Hnn', Hi', Hc', Hw', Hisl', Hicap', Hcsl', Hccap', Hch'⟩
      ihave %Hpl' := ownNodes_length o tv.cow' f less _ _ _ $$ Hch'
      ihave %Hcl' := ownSlice_len _ _ _ $$ Hcsl'
      ihave %Hil' := ownSlice_len _ _ _ $$ Hisl'
      simp only [List.length_map] at Hil'
      wp_join iprop(∃ (r'' : Loc) (h'' : Nat) (tr'' : Tree (V × K)),
          t_ptr ↦ t ∗
          t ↦ ({ degree' := tv.degree', length' := tv.length', root' := r'', cow' := tv.cow' } :
            BTree V) ∗
          ownNode o tv.cow' f less (DFrac.own 1) r'' tr'' ∗
          ⌜tr''.Shape d h'' ∧ tr''.RootBounds d h'' ∧ tr''.elems = (removeOp tgt s).1⌝)
        at next with [-HΦ out outb]
        as ⟨%r'', %h'', %tr'', t, Ht, Hn, %Hpure⟩
      · wp_auto
        wp_if_destruct
        · -- the root has no items left
          have his : is' = [] := by
            apply List.eq_nil_of_length_eq_zero; rw [Hil'.1, Hif]; rfl
          subst his
          wp_if_destruct
          · -- collapse the root into its only child
            cases h with
            | zero =>
              exfalso
              rw [shape_zero] at hs'; subst hs'
              simp at Hpl'; subst Hpl'
              simp at Hcl'; word
            | succ h' =>
            have hcs1 := ((shape_succ d h' [] cs').1 hs').1
            obtain ⟨c0, rfl⟩ : ∃ c0, cs' = [c0] := by
              match cs', hcs1 with
              | [c0], _ => exact ⟨c0, rfl⟩
            obtain ⟨p0, rfl⟩ : ∃ p0, ps' = [p0] := by
              match ps', Hpl' with
              | [p0], _ => exact ⟨p0, rfl⟩
            have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl'.len := by
              constructor
              · decide
              · simp at Hcl'; word
            simp only [hb0, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index csl' (sint.Z (W64 0)) [p0] _ p0 hb0.1 $$ [Hcsl'] as Hcsl'
            · iframe; ipureintro; rfl
            wp_auto
            wp_apply wp_freeNode o tv.cow' f less r' $$ [Hi' Hc' Hw' Hisl' Hicap' Hcsl' Hccap']
              as %r -
            · iframe # ∗
              ileft
              iexists [], [p0]
              unfold nodeShallow nodeFields
              iexists isl', csl'
              iframe
              ipureintro; exact Hnn'
            rw [ownNodes_cons]
            icases Hch' with ⟨Hp0, -⟩
            try wp_join_done
            iexists p0, h', c0
            iframe
            have hc0 := shape_child (c := c0) hs' (j := 0) rfl
            ipureintro
            refine ⟨hc0.2, ⟨hc0.1.2, fun _ => by omega⟩, ?_⟩
            rw [← he']; simp
          · -- no children: a leaf root
            have hps : ps' = [] := by
              apply List.eq_nil_of_length_eq_zero; rw [Hcl'.1]; word
            subst hps
            have hcs : cs' = [] := by simpa using Hpl'.symm
            subst hcs
            try wp_join_done
            iexists r', h, Tree.node [] []
            iframe
            isplitl
            · iapply ownNode_of_owned
              iapply ownedNode_close o tv.cow' f less _ r' [] [] [] isl' csl'
              unfold ownedRes
              iframe
              ipureintro; exact Hnn'
            · ipureintro
              have hh0 : h = 0 := by
                rcases Nat.eq_zero_or_pos h with hh | hh
                · exact hh
                · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
                  have := ((shape_succ d h' [] []).1 hs').1; simp at this
              subst hh0
              exact ⟨hs', ⟨by simp at hl1 ⊢; try omega, fun hh => absurd hh (by omega)⟩, he'⟩
        · -- the root keeps items
          have hne : 1 ≤ is'.length := by
            have h2 : sint.nat isl'.len ≠ 0 := by intro h0; apply Hif; word
            omega
          try wp_join_done
          iexists r', h, Tree.node is' cs'
          iframe
          isplitl
          · iapply ownNode_of_owned
            iapply ownedNode_close o tv.cow' f less _ r' _ _ ps' isl' csl'
            unfold ownedRes
            iframe
            ipureintro; exact Hnn'
          · ipureintro
            exact ⟨hs', ⟨by have := Hrb.1; simp at hl1 ⊢; omega, fun _ => hne⟩, he'⟩
      obtain ⟨hS, hRB, hE⟩ := Hpure
      have hsub := removeOp_sublist tgt s
      have hsorted' : Sorted o.lt (removeOp tgt s).1 := sorted_sublist hsub Hsorted
      ihave #Hitems' := allItems_mono_rm o (l1 := (removeOp tgt s).1) (l2 := s)
        (fun e he => hsub.subset he) $$ Hitems
      subst hout hfnd
      cases hc : (removeOp tgt s).snd.isSome with
      | true =>
        have hl := removeOp_some o.order tgt s Hsorted hc
        wp_auto
        iapply HΦ
        iexists ⟨tv.degree', tv.length' - W64 1, r'', tv.cow'⟩, f, less, d
        have Hlen' : tv.length' - W64 1 = W64 ↑(removeOp tgt s).1.length := by
          rw [Hlen, ← hl]; word
        iframe Ht Hcow Hitems'
        iframe %Hdeg %Hlen' %hsorted'
        iright
        iexists h'', tr''
        iframe Hn
        ipureintro; exact ⟨hS, hRB, hE⟩
      | false =>
        have hl := removeOp_none tgt s hc
        wp_auto
        iapply HΦ
        iexists ⟨tv.degree', tv.length', r'', tv.cow'⟩, f, less, d
        have Hlen' : tv.length' = W64 ↑(removeOp tgt s).1.length := by rw [hl]; exact Hlen
        iframe Ht Hcow Hitems'
        iframe %Hdeg %Hlen' %hsorted'
        iright
        iexists h'', tr''
        iframe Hn
        ipureintro; exact ⟨hS, hRB, hE⟩




end proof

end btree
end EtcdGrove
end Perennial
