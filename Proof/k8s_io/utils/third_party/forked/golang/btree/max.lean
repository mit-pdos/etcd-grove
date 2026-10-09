module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.max
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Read

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem max.wp_proof : max.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less d dq n s hd
  wp_start as Hr
  wp_alloc_anon
  wp_pures
  wp_alloc_anon
  wp_auto
  rename_i lf lz
  irename : (lf ↦ zero_val Bool : IProp GF) => Hfound
  irename : (lz ↦ zero_val V : IProp GF) => Hzero
  unfold ownRoot
  icases Hr with (%Hnil | ⟨%h, %tr, ⟨%Hsh, %Hrb, %Hel⟩, Hn⟩)
  · obtain ⟨Hr, rfl⟩ := Hnil
    subst Hr
    wp_auto
    rw [show (zero_val Bool) = false from rfl]
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none, List.isEmpty_nil,
      Bool.not_true]
    iapply HΦ
    ileft; ipureintro; simp
  · ihave %Hnn := ownNode_not_null $$ Hn
    wp_if_destruct
    · exact absurd rfl Hnn
    obtain ⟨is0, cs0⟩ := tr
    icases ownNode_peek o c f less dq n is0 cs0 $$ Hn with
      ⟨%dq', %isl, %csl, %cow, %ps, Hnf, Hisl, Hcsl, Hch, Hclose⟩
    unfold nodeFields
    icases Hnf with ⟨Hnn', Hfi, Hfc, Hfw⟩
    ihave HI : (∃ (m : Loc) (h' : Nat) (is : List (V × K)) (cs : List (Tree (V × K)))
        (dq' : DFrac) (isl csl : GoSlice) (cow : Loc) (ps : List Loc),
        "n" ∷ n_ptr ↦ m ∗
        "Hnn'" ∷ ⌜m ≠ null⌝ ∗
        "Hfi" ∷ m.[node V, go!"items"] ↦{dq'} isl ∗
        "Hfc" ∷ m.[node V, go!"children"] ↦{dq'} csl ∗
        "Hfw" ∷ m.[node V, go!"cow"] ↦{dq'} cow ∗
        "Hisl" ∷ isl ↦*{dq'} is.map Prod.fst ∗ "Hcsl" ∷ csl ↦*{dq'} ps ∗
        "Hch" ∷ ownNodes o c f less dq ps cs ∗
        "Hclose" ∷ (nodeFields (V := V) m dq' isl csl cow ∗ isl ↦*{dq'} is.map Prod.fst ∗
          csl ↦*{dq'} ps ∗ ownNodes o c f less dq ps cs -∗
          ownNode o c f less dq m (.node is cs)) ∗
        "Hw" ∷ (ownNode o c f less dq m (.node is cs) -∗ ownNode o c f less dq n (.node is0 cs0)) ∗
        "%Hinv" ∷ ⌜(Tree.node is cs).Shape d h' ∧ s.getLast? = (Tree.elemsAux is cs).getLast?⌝ : IProp GF)
      $$ [n Hnn' Hfi Hfc Hfw Hisl Hcsl Hch Hclose]
    · iexists n, h, is0, cs0, dq', isl, csl, cow, ps
      iframe
      isplitl []
      · iintro H; iexact H
      ipureintro; exact ⟨Hsh, by rw [← Hel]; rfl⟩
    wp_for HI
    obtain ⟨Hshape, Hhead⟩ := Hinv
    ihave %Hlenc := ownSlice_len _ _ _ $$ Hcsl
    ihave %Hlenps := ownNodes_length o c f less dq ps cs $$ Hch
    ihave %Hleni := ownSlice_len _ _ _ $$ Hisl
    simp only [List.length_map] at Hleni
    wp_if_destruct
    · -- an internal node: go down to the last child
      obtain ⟨h'', rfl⟩ : ∃ h'', h' = h'' + 1 := by
        cases h' with
        | zero =>
          have hcs : cs = [] := by simpa [Tree.Shape] using Hshape
          subst hcs
          have h0 : ps.length = 0 := by simpa using Hlenps
          word
        | succ h'' => exact ⟨h'', rfl⟩
      have hcl : cs.length = is.length + 1 := Hshape.1
      have hj : is.length < ps.length := by omega
      list_elem ps is.length as p
      list_elem cs is.length as ch
      have hb : 0 ≤ sint.Z (csl.len - W64 1) ∧ sint.Z (csl.len - W64 1) < sint.Z csl.len := by
        word
      simp only [hb, _root_.and_self, ↓reduceIte]
      have hidx : (sint.Z (csl.len - W64 1)).toNat = is.length := by word
      wp_apply wp_load_slice_index csl (sint.Z (csl.len - W64 1)) ps dq' p hb.1 $$ [Hcsl] as Hcsl
      · iframe; ipureintro; rw [hidx]; exact Hp_lookup
      wp_for_post
      icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).1 $$ Hch
        with ⟨Hc0, Hch⟩
      have hchm : ch ∈ cs := List.mem_of_getElem? Hch_lookup
      have hchs := (Hshape.2 _ hchm).2
      have hne := child_elems_ne_nil hd Hshape hchm
      obtain ⟨is1, cs1⟩ := ch
      icases ownNode_peek o c f less dq p is1 cs1 $$ Hc0 with
        ⟨%dq1, %isl1, %csl1, %cow1, %ps1, Hnf1, Hisl1, Hcsl1, Hch1, Hclose1⟩
      unfold nodeFields
      icases Hnf1 with ⟨Hnn1, Hfi1, Hfc1, Hfw1⟩
      iframe HΦ Hfound Hzero
      iexists p, h'', is1, cs1, dq1, isl1, csl1, cow1, ps1
      iframe n Hnn1 Hfi1 Hfc1 Hfw1 Hisl1 Hcsl1 Hch1 Hclose1
      isplitl [Hw Hclose Hnn' Hfi Hfc Hfw Hisl Hcsl Hch]
      · iintro Hc0
        iapply Hw
        iapply Hclose
        iframe
        iapply (ownNodes_extract o c f less dq ps cs _ p _ Hp_lookup Hch_lookup).2
        iframe
      ipureintro
      refine ⟨hchs, ?_⟩
      rw [Hhead, getLast_elemsAux is cs hcl _ Hch_lookup hne]
      rfl
    · -- a leaf
      have hcs : cs = [] := by
        cases cs with
        | nil => rfl
        | cons _ _ =>
          have h0 : 0 < ps.length := by simp [Hlenps]
          word
      subst hcs
      rw [Tree.elemsAux_nil] at Hhead
      wp_if_destruct
      · -- no items: the tree is empty
        have his : is = [] := by
          cases is with
          | nil => rfl
          | cons _ _ => simp at Hleni; word
        subst his
        have hs : s = [] := by simpa using Hhead
        subst hs
        rw [show (zero_val Bool) = false from rfl]
        simp only [List.getLast?_nil, Option.map_none, Option.getD_none, List.isEmpty_nil,
          Bool.not_true]
        iapply HΦ
        iright
        iexists h, Tree.node is0 cs0
        isplitr
        · ipureintro; exact ⟨Hsh, Hrb, Hel⟩
        iapply Hw
        iapply Hclose
        unfold nodeFields
        iframe
      · obtain ⟨is', x, rfl⟩ : ∃ is' x, is = is' ++ [x] := by
          rcases List.eq_nil_or_concat is with h0 | ⟨L, b, h0⟩
          · subst h0; simp at Hleni; word
          · exact ⟨L, b, by simpa using h0⟩
        have hl' : is'.length + 1 = sint.nat isl.len := by simpa using Hleni.1
        have hb : 0 ≤ sint.Z (isl.len - W64 1) ∧ sint.Z (isl.len - W64 1) < sint.Z isl.len := by
          word
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index isl (sint.Z (isl.len - W64 1)) ((is' ++ [x]).map Prod.fst)
          dq' x.1 (by word) $$ [Hisl] as Hisl
        · iframe; ipureintro
          rw [show (sint.Z (isl.len - W64 1)).toNat = is'.length by word]
          simp
        have hs : s.getLast? = some x := by simpa using Hhead
        have hne : s.isEmpty = false := by
          cases s with
          | nil => simp at hs
          | cons _ _ => rfl
        rw [hs, hne]
        simp only [Option.map_some, Option.getD_some, Bool.not_false]
        iapply HΦ
        iright
        iexists h, Tree.node is0 cs0
        isplitr
        · ipureintro; exact ⟨Hsh, Hrb, Hel⟩
        iapply Hw
        iapply Hclose
        unfold nodeFields
        iframe

end proof

end btree
end EtcdGrove
end Perennial
