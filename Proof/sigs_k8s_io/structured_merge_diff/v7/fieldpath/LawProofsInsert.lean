/-
**`Set.Insert`'s and `SetNodeMap.Descend`'s facts**: an owned raw trie's children (`trieOwnC`:
keys, splitting at a node, inserting a node), the binary search's index read over a children
list (`nodesLookup`, `nodesSet`), and the paths and canonical form of a trie after a path is put
in it.

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpI

/-! ## The binary search's index over a children list -/

abbrev ckeys (cs : List (PE × Trie)) : List PE := cs.map (·.1)

theorem lookup_none (pe : PE) : ∀ (cs : List (PE × Trie)), pe ∉ ckeys cs → nodesLookup pe cs = none
  | [], _ => rfl
  | (e, t) :: cs, h => by
    have h1 : e ≠ pe := fun he => h (by simp [ckeys, he])
    have h2 : pe ∉ ckeys cs := fun hm => h (by simp only [ckeys, List.map_cons, List.mem_cons]; exact Or.inr hm)
    simp only [nodesLookup, h1, ↓reduceIte]
    exact lookup_none pe cs h2

theorem lookup_at (pe : PE) (t : Trie) : ∀ (cs : List (PE × Trie)) (i : Nat),
    (∀ k (hk : k < i), ∀ x, cs[k]? = some x → x.1 ≠ pe) → cs[i]? = some (pe, t) →
    nodesLookup pe cs = some t
  | [], _, _, h => by simp at h
  | (e, t') :: cs, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [nodesLookup]
  | (e, t') :: cs, i + 1, hb, h => by
    have h1 : e ≠ pe := hb 0 (by omega) (e, t') rfl
    simp only [nodesLookup, h1, ↓reduceIte]
    exact lookup_at pe t cs i (fun k hk x hx => hb (k + 1) (by omega) x hx) h

theorem set_at (pe : PE) (t t' : Trie) : ∀ (cs : List (PE × Trie)) (i : Nat),
    (∀ k (hk : k < i), ∀ x, cs[k]? = some x → x.1 ≠ pe ∧ ¬ PE.compare pe x.1 < 0) →
    cs[i]? = some (pe, t) → nodesSet pe t' cs = cs.set i (pe, t')
  | [], _, _, h => by simp at h
  | (e, t0) :: cs, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [nodesSet]
  | (e, t0) :: cs, i + 1, hb, h => by
    obtain ⟨h1, h2⟩ := hb 0 (by omega) (e, t0) rfl
    simp only [nodesSet, h1, h2, ↓reduceIte, List.set_cons_succ]
    rw [set_at pe t t' cs i (fun k hk x hx => hb (k + 1) (by omega) x hx) h]

theorem set_ins (pe : PE) (t' : Trie) : ∀ (cs : List (PE × Trie)) (i : Nat), i ≤ cs.length →
    (∀ k (hk : k < i), ∀ x, cs[k]? = some x → x.1 ≠ pe ∧ ¬ PE.compare pe x.1 < 0) →
    (∀ x, cs[i]? = some x → x.1 ≠ pe ∧ PE.compare pe x.1 < 0) →
    nodesSet pe t' cs = cs.take i ++ (pe, t') :: cs.drop i
  | [], i, hi, _, _ => by
    have : i = 0 := by simp at hi; omega
    subst this; simp [nodesSet]
  | (e, t0) :: cs, 0, _, _, hn => by
    obtain ⟨h1, h2⟩ := hn (e, t0) rfl
    simp [nodesSet, h1, h2]
  | (e, t0) :: cs, i + 1, hi, hb, hn => by
    obtain ⟨h1, h2⟩ := hb 0 (by omega) (e, t0) rfl
    simp only [nodesSet, h1, h2, ↓reduceIte, List.take_succ_cons, List.drop_succ_cons,
      List.cons_append]
    rw [set_ins pe t' cs i (by simp at hi; omega) (fun k hk x hx => hb (k + 1) (by omega) x hx) hn]

/-- **The binary search found `pe` at `i`**. -/
theorem bs_found_cs {cs : List (PE × Trie)} {pe : PE} {i : Nat} (hw : fpA.AllWf (ckeys cs))
    (hp : pe.wf = true) (hb : fpA.BsIdx (ckeys cs) pe i)
    (hf : ∃ x, (ckeys cs)[i]? = some x ∧ PE.compare x pe = 0) :
    ∃ t, cs[i]? = some (pe, t) ∧ nodesLookup pe cs = some t ∧
      ∀ t', nodesSet pe t' cs = cs.set i (pe, t') := by
  obtain ⟨x, hx, hc⟩ := hf
  have hxw : x.wf = true := hw x (List.mem_of_getElem? hx)
  have hxe : x = pe := (PE_compare_eq_zero_law_holds x pe hxw hp).1 hc
  subst hxe
  simp only [ckeys, List.getElem?_map] at hx
  obtain ⟨⟨e, t⟩, hct, he⟩ := Option.map_eq_some_iff.1 hx
  simp only at he; subst he
  have hlt : ∀ k (hk : k < i), ∀ y, cs[k]? = some y → PE.lt y.1 e := fun k hk y hy =>
    (hb.2 k y.1 (by simp [ckeys, List.getElem?_map, hy])).1 hk
  have hyw : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → y.1.wf = true := fun k y hy =>
    hw y.1 (by simp only [ckeys, List.mem_map]; exact ⟨y, List.mem_of_getElem? hy, rfl⟩)
  refine ⟨t, hct, lookup_at e t cs i (fun k hk y hy h => ?_) hct, fun t' => set_at e t t' cs i
    (fun k hk y hy => ⟨fun h => ?_, fun h => ?_⟩) hct⟩
  · have := hlt k hk y hy; rw [h] at this; exact fpA.lt_irrefl e hp this
  · have := hlt k hk y hy; rw [h] at this; exact fpA.lt_irrefl e hp this
  · have h1 := hlt k hk y hy
    exact fpA.lt_asymm (hyw k y hy) hp h1 h

/-- **The binary search did not find `pe`**: it goes in at `i`. -/
theorem bs_notfound_cs {cs : List (PE × Trie)} {pe : PE} {i : Nat} (hw : fpA.AllWf (ckeys cs))
    (hp : pe.wf = true) (hs : PE.Sorted (ckeys cs)) (hb : fpA.BsIdx (ckeys cs) pe i)
    (hn : pe ∉ ckeys cs) :
    nodesLookup pe cs = none ∧ ∀ t', nodesSet pe t' cs = cs.take i ++ (pe, t') :: cs.drop i := by
  refine ⟨lookup_none pe cs hn, fun t' => ?_⟩
  have hyw : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → y.1.wf = true := fun k y hy =>
    hw y.1 (by simp only [ckeys, List.mem_map]; exact ⟨y, List.mem_of_getElem? hy, rfl⟩)
  have hne : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → y.1 ≠ pe := fun k y hy h => hn (by
    simp only [ckeys, List.mem_map]; exact ⟨y, List.mem_of_getElem? hy, h⟩)
  have hkey : ∀ (k : Nat) (y : PE × Trie), cs[k]? = some y → (ckeys cs)[k]? = some y.1 := fun k y hy => by
    simp [ckeys, List.getElem?_map, hy]
  refine set_ins pe t' cs i (by simpa [ckeys] using hb.1) (fun k hk y hy => ⟨hne k y hy, fun h => ?_⟩)
    (fun y hy => ⟨hne i y hy, ?_⟩)
  · exact fpA.lt_asymm (hyw k y hy) hp ((hb.2 k y.1 (hkey k y hy)).1 hk) h
  · have hnl : ¬ PE.lt y.1 pe := fun h => by have := (hb.2 i y.1 (hkey i y hy)).2 h; omega
    rcases fpA.lt_total (hyw i y hy) hp with h | h | h
    · exact absurd h hnl
    · exact absurd h (hne i y hy)
    · exact h

/-! ## An owned raw trie's children -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem trieOwnC_nil_eq : trieOwnC (GF := GF) [] [] = iprop(True) := by simp only [trieOwnC]

theorem trieOwnC_cons_eq (n : fieldpath.setNode) (ns : List fieldpath.setNode) (pe : PE) (t : Trie)
    (cs : List (PE × Trie)) :
    trieOwnC (GF := GF) (n :: ns) ((pe, t) :: cs) =
      iprop(isPE n.pathElement' pe ∗ trieOwn n.set' t ∗ trieOwnC ns cs) := by
  simp only [trieOwnC]

theorem trieOwnC_keys : ∀ (ns : List fieldpath.setNode) (cs : List (PE × Trie)),
    trieOwnC (GF := GF) ns cs ⊢
      isPEL (ns.map (·.pathElement')) (ckeys cs) ∗ trieOwnC ns cs
  | [], [] => by
    rw [trieOwnC_nil_eq]; iintro -
    simp only [List.map_nil, ckeys]; rw [fpL.isPEL_nil_eq]; iframe; isplit <;> itrivial
  | [], _ :: _ => by unfold trieOwnC; iintro %h; exact h.elim
  | _ :: _, [] => by unfold trieOwnC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs => by
    rw [trieOwnC_cons_eq]
    iintro ⟨#Hpe, Ht, Hc⟩
    icases trieOwnC_keys ns cs $$ Hc with ⟨#Hk, Hc⟩
    simp only [List.map_cons, ckeys]
    rw [fpL.isPEL_cons_eq]
    iframe
    iframe #

theorem trieOwnC_app : ∀ (a b : List fieldpath.setNode) (c d : List (PE × Trie)), a.length = c.length →
    trieOwnC (GF := GF) (a ++ b) (c ++ d) ⊣⊢ trieOwnC a c ∗ trieOwnC b d
  | [], b, [], d, _ => by
    simp only [List.nil_append]; rw [trieOwnC_nil_eq]
    exact ⟨by iintro H; iframe, by iintro ⟨-, H⟩; iexact H⟩
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | n :: a, b, (pe, t) :: c, d, h => by
    simp only [List.cons_append]
    rw [trieOwnC_cons_eq, trieOwnC_cons_eq]
    have ih := trieOwnC_app a b c d (by simpa using h)
    constructor
    · iintro ⟨Hpe, Ht, H⟩
      icases ih.1 $$ H with ⟨H1, H2⟩
      iframe
    · iintro ⟨⟨Hpe, Ht, H1⟩, H2⟩
      iframe
      iapply ih.2; iframe

/-- The node at `i`, and the way back with any trie in its place. -/
theorem trieOwnC_at (ns : List fieldpath.setNode) (cs : List (PE × Trie)) (i : Nat)
    (n : fieldpath.setNode) (pe : PE) (t : Trie) (hn : ns[i]? = some n) (hc : cs[i]? = some (pe, t)) :
    trieOwnC (GF := GF) ns cs ⊢
      trieOwn n.set' t ∗ (∀ t', trieOwn n.set' t' -∗ trieOwnC ns (cs.set i (pe, t'))) := by
  have hi : i < ns.length := (List.getElem?_eq_some_iff.1 hn).1
  have hi' : i < cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hn' : ns[i] = n := by rw [List.getElem?_eq_getElem hi] at hn; exact Option.some.inj hn
  have hc' : cs[i] = (pe, t) := by rw [List.getElem?_eq_getElem hi'] at hc; exact Option.some.inj hc
  have en : ns = ns.take i ++ n :: ns.drop (i + 1) := by
    rw [← hn', ← fpA.drop_cons' ns i hi, List.take_append_drop]
  have ec : cs = cs.take i ++ (pe, t) :: cs.drop (i + 1) := by
    rw [← hc', ← fpA.drop_cons' cs i hi', List.take_append_drop]
  have hl : (ns.take i).length = (cs.take i).length := by simp; omega
  have hl2 : (cs.take i).length = i := by simp; omega
  generalize ns.take i = a, ns.drop (i + 1) = b, cs.take i = c, cs.drop (i + 1) = d at en ec hl hl2
  subst en ec
  have e2 : ∀ t', (c ++ (pe, t) :: d).set i (pe, t') = c ++ (pe, t') :: d := fun t' => by
    rw [List.set_append_right _ _ (by omega), hl2, Nat.sub_self]; rfl
  iintro H
  icases (trieOwnC_app _ _ _ _ hl).1 $$ H with ⟨H1, H2⟩
  rw [trieOwnC_cons_eq]
  icases H2 with ⟨#Hpe, Ht, H3⟩
  iframe Ht
  iintro %t' Ht'
  rw [e2 t']
  iapply (trieOwnC_app _ _ _ _ hl).2
  iframe H1
  rw [trieOwnC_cons_eq]
  iframe
  iframe #

theorem trieOwnC_length (ns : List fieldpath.setNode) (cs : List (PE × Trie)) :
    trieOwnC (GF := GF) ns cs ⊢ ⌜ns.length = cs.length⌝ ∗ trieOwnC ns cs := by
  iintro H
  icases trieOwnC_keys ns cs $$ H with ⟨#Hk, H⟩
  ihave %hl := fpL.isPEL_length $$ Hk
  iframe
  ipureintro; simpa [ckeys] using hl

/-- A new node put in at `i`. -/
theorem trieOwnC_ins (ns : List fieldpath.setNode) (cs : List (PE × Trie)) (i : Nat)
    (n : fieldpath.setNode) (pe : PE) (t : Trie) :
    trieOwnC (GF := GF) ns cs ∗ isPE n.pathElement' pe ∗ trieOwn n.set' t ⊢
      trieOwnC (ns.take i ++ n :: ns.drop i) (cs.take i ++ (pe, t) :: cs.drop i) := by
  iintro ⟨H, #Hpe, Ht⟩
  icases trieOwnC_length ns cs $$ H with ⟨%hl, H⟩
  have hl' : (ns.take i).length = (cs.take i).length := by simp [hl]
  have e : trieOwnC (GF := GF) ns cs = trieOwnC (ns.take i ++ ns.drop i) (cs.take i ++ cs.drop i) := by
    rw [List.take_append_drop, List.take_append_drop]
  rw [e]
  icases (trieOwnC_app _ _ _ _ hl').1 $$ H with ⟨H1, H2⟩
  iapply (trieOwnC_app _ _ _ _ hl').2
  iframe H1
  rw [trieOwnC_cons_eq]
  iframe
  iframe #

/-- A `setNode`'s two fields, and the way back. -/
theorem setnode_fields (l : Loc) (v : fieldpath.setNode) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[fieldpath.setNode, go!"pathElement"] ↦{dq} v.pathElement' ∗
      l.[fieldpath.setNode, go!"set"] ↦{dq} v.set' ∗
      (l.[fieldpath.setNode, go!"pathElement"] ↦{dq} v.pathElement' -∗
        l.[fieldpath.setNode, go!"set"] ↦{dq} v.set' -∗ l ↦{dq} v) := by
  iintro Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hn⟩
  iStructNamed Hl
  iframe pathElement set
  iintro Ha Hb
  iapply typedPointsto_combine _ _ _ hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Ha Hb

/-- A `SetNodeMap`'s one field, and the way back with any new value. -/
theorem nodemap_members_upd (l : Loc) (v : fieldpath.SetNodeMap) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ l.[fieldpath.SetNodeMap, go!"members"] ↦{dq} v.members' ∗
      (∀ w, l.[fieldpath.SetNodeMap, go!"members"] ↦{dq} w -∗
        l ↦{dq} ({ members' := w } : fieldpath.SetNodeMap)) := by
  iintro Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hn⟩
  iStructNamed Hl
  iframe members
  iintro %w Hm
  iapply typedPointsto_combine _ _ _ hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hm

/-- `&Set{}`: the empty trie, owned. -/
theorem trieOwn_empty (p : Loc) : (p ↦ zero_val fieldpath.Set' : IProp GF) ⊢ trieOwn p Trie.empty := by
  iintro Hp
  unfold Trie.empty
  rw [trieOwn.eq_1]
  iexists (zero_val fieldpath.Set'), [], []
  have h1 : (zero_val fieldpath.Set').Members'.members' = slice.nil := rfl
  have h2 : (zero_val fieldpath.Set').Children'.members' = slice.nil := rfl
  rw [h1, h2, isPEL.eq_1, trieOwnC.eq_1]
  iframe
  ihave Hn1 := ownSlice_nil (V := fieldpath.PathElement) (GF := GF) (DFrac.own 1)
  ihave Hn2 := ownSlice_nil (V := fieldpath.setNode) (GF := GF) (DFrac.own 1)
  ihave Hc1 := ownSliceCap_nil (V := fieldpath.PathElement) (GF := GF)
  ihave Hc2 := ownSliceCap_nil (V := fieldpath.setNode) (GF := GF)
  iframe #

end own

end fpI

end smd
end EtcdGrove
end Perennial
