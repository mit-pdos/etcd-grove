/-
**`fieldpath`'s tries, proved facts** (the representation of `Set`, `SetNodeMap`): a canonical
trie's paths as a list, a node list as pairs (path element, set of paths below it), and the views
of `isSet`/`isNodesV` the trie operations' proofs work at: a set is its members (`PathSet.tops`)
and its children (`PathSet.deep`), the children a sorted list of (element, `isSet`) nodes.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
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

namespace fpC

/-! ## A trie's paths as a list -/

mutual
/-- The paths of a trie, listed. -/
def pathList : Trie → List Path
  | .mk ms cs => ms.map (fun e => [e]) ++ pathListC cs
/-- The paths below a list of children, listed. -/
def pathListC : List (PE × Trie) → List Path
  | [] => []
  | (e, t) :: cs => (pathList t).map (e :: ·) ++ pathListC cs
end

mutual
theorem mem_pathList : ∀ (t : Trie) (q : Path), q ∈ pathList t ↔ Trie.paths t q
  | .mk ms cs, q => by
    simp only [pathList, Trie.paths, List.mem_append, List.mem_map, mem_pathListC cs q]
    constructor
    · rintro (⟨e, he, rfl⟩ | h)
      · exact Or.inl ⟨e, rfl, he⟩
      · exact Or.inr h
    · rintro (⟨e, rfl, he⟩ | h)
      · exact Or.inl ⟨e, he, rfl⟩
      · exact Or.inr h
theorem mem_pathListC : ∀ (cs : List (PE × Trie)) (q : Path), q ∈ pathListC cs ↔ Trie.pathsC cs q
  | [], q => by simp [pathListC, Trie.pathsC]
  | (e, t) :: cs, q => by
    simp only [pathListC, Trie.pathsC, List.mem_append, List.mem_map, mem_pathListC cs q]
    constructor
    · rintro (⟨r, hr, rfl⟩ | h)
      · exact Or.inl ⟨r, rfl, (mem_pathList t r).1 hr⟩
      · exact Or.inr h
    · rintro (⟨r, rfl, hr⟩ | h)
      · exact Or.inl ⟨r, (mem_pathList t r).2 hr, rfl⟩
      · exact Or.inr h
end

/-- The set of a trie's paths. -/
def tset (t : Trie) : PathSet := FSet.ofList (pathList t)

theorem mem_tset (t : Trie) (q : Path) : q ∈ tset t ↔ Trie.paths t q := by
  unfold tset; rw [FSet.mem_ofList', mem_pathList]

theorem pathsC_ne_nil : ∀ cs : List (PE × Trie), ¬ Trie.pathsC cs []
  | [] => by simp [Trie.pathsC]
  | (e, t) :: cs => by
    have := pathsC_ne_nil cs
    simp only [Trie.pathsC]
    simp [this]

theorem paths_ne_nil (t : Trie) : ¬ Trie.paths t [] := by
  cases t with
  | mk ms cs =>
    have := pathsC_ne_nil cs
    simp only [Trie.paths]
    simp [this]

/-! ## Node lists: (path element, the set of paths below it) -/

abbrev NL := List (PE × PathSet)

/-- The paths of a node list: `k :: r` for `r` in `k`'s set. -/
def nlPaths : NL → PathSet
  | [] => FSet.empty
  | (k, S) :: l => FSet.union (FSet.map (k :: ·) S) (nlPaths l)

theorem mem_nlPaths : ∀ (l : NL) (q : Path),
    q ∈ nlPaths l ↔ ∃ k S r, (k, S) ∈ l ∧ r ∈ S ∧ q = k :: r
  | [], q => by simp [nlPaths, FSet.mem_empty]
  | (k, S) :: l, q => by
    simp only [nlPaths, FSet.mem_union', FSet.mem_map', mem_nlPaths l q, List.mem_cons,
      Prod.mk.injEq]
    constructor
    · rintro (⟨r, hr, rfl⟩ | ⟨k', S', r, h, hr, rfl⟩)
      · exact ⟨k, S, r, Or.inl ⟨rfl, rfl⟩, hr, rfl⟩
      · exact ⟨k', S', r, Or.inr h, hr, rfl⟩
    · rintro ⟨k', S', r, (⟨rfl, rfl⟩ | h), hr, rfl⟩
      · exact Or.inl ⟨r, hr, rfl⟩
      · exact Or.inr ⟨k', S', r, h, hr, rfl⟩

theorem mem_nlPaths_nil (q : Path) : q ∉ nlPaths [] := by simp [mem_nlPaths]

/-- A well-formed node list: keys strictly sorted and well-formed, every set non-empty, without
the empty path. -/
def NLok (l : NL) : Prop :=
  PE.Sorted (l.map (·.1)) ∧ ∀ k S, (k, S) ∈ l → k.wf = true ∧ (∃ q, q ∈ S) ∧ [] ∉ S

/-- A canonical trie's children as a node list. -/
def nlOf (cs : List (PE × Trie)) : NL := cs.map (fun p => (p.1, tset p.2))

theorem pathsC_nlOf : ∀ (cs : List (PE × Trie)) (q : Path),
    Trie.pathsC cs q ↔ q ∈ nlPaths (nlOf cs)
  | [], q => by simp [Trie.pathsC, nlOf, mem_nlPaths]
  | (e, t) :: cs, q => by
    have ih := pathsC_nlOf cs q
    simp only [nlOf] at ih
    simp only [Trie.pathsC, nlOf, List.map_cons, nlPaths, FSet.mem_union', FSet.mem_map', ih,
      mem_tset]
    constructor
    · rintro (⟨r, rfl, h⟩ | h)
      · exact Or.inl ⟨r, h, rfl⟩
      · exact Or.inr h
    · rintro (⟨r, h, rfl⟩ | h)
      · exact Or.inl ⟨r, rfl, h⟩
      · exact Or.inr h

theorem nlOf_keys (cs : List (PE × Trie)) : (nlOf cs).map (·.1) = cs.map (·.1) := by
  simp [nlOf]

theorem canonicalC_mem : ∀ (cs : List (PE × Trie)) (e : PE) (t : Trie), Trie.CanonicalC cs →
    (e, t) ∈ cs → Trie.Canonical t ∧ ∃ q, Trie.paths t q
  | [], _, _, _, h => by simp at h
  | (e', t') :: cs, e, t, hc, hm => by
    simp only [Trie.CanonicalC] at hc
    rcases List.mem_cons.1 hm with hm | hm
    · cases hm; exact ⟨hc.1, hc.2.1⟩
    · exact canonicalC_mem cs e t hc.2.2 hm

theorem tset_nonempty_of (t : Trie) (q : Path) (h : Trie.paths t q) : ∃ q, q ∈ tset t :=
  ⟨q, (mem_tset t q).2 h⟩

theorem pathsC_single : ∀ (cs : List (PE × Trie)) (e : PE), ¬ Trie.pathsC cs [e]
  | [], e => by simp [Trie.pathsC]
  | (e', t) :: cs, e => by
    have := pathsC_single cs e
    have := paths_ne_nil t
    simp only [Trie.pathsC]
    simp_all

theorem pathsC_len : ∀ (cs : List (PE × Trie)) (q : Path), Trie.pathsC cs q → 2 ≤ q.length
  | [], q, h => by simp [Trie.pathsC] at h
  | (e', t) :: cs, q, h => by
    simp only [Trie.pathsC] at h
    rcases h with ⟨r, rfl, hr⟩ | h
    · cases r with
      | nil => exact absurd hr (paths_ne_nil t)
      | cons _ _ => simp
    · exact pathsC_len cs q h

/-- A canonical trie's paths: its members' one-element paths and its children's. -/
theorem paths_mk (ms : List PE) (cs : List (PE × Trie)) (q : Path) :
    Trie.paths (.mk ms cs) q ↔ (∃ e, q = [e] ∧ e ∈ ms) ∨ Trie.pathsC cs q := by
  simp only [Trie.paths]

/-! ## Membership in the vocabulary's sets (the laws, as simp lemmas) -/

theorem mem_tops (S : PathSet) (e : PE) : e ∈ S.tops ↔ [e] ∈ S := PathSet_mem_tops_law_holds S e
theorem mem_deep (S : PathSet) (q : Path) : q ∈ S.deep ↔ q ∈ S ∧ 2 ≤ q.length :=
  PathSet_mem_deep_law_holds S q
theorem mem_heads (S : PathSet) (e : PE) : e ∈ S.heads ↔ ∃ q, q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_heads_law_holds S e
theorem mem_under (S : PathSet) (e : PE) (q : Path) : q ∈ S.under e ↔ q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_under_law_holds S e q
theorem mem_rdiff (A B : PathSet) (q : Path) :
    q ∈ PathSet.rdiff A B ↔ q ∈ A ∧ ∀ r ∈ q.nePrefixes, r ∉ B := PathSet_mem_rdiff_law_holds A B q
theorem mem_punion (A B : PathSet) (q : Path) : q ∈ PathSet.union A B ↔ q ∈ A ∨ q ∈ B :=
  FSet.mem_union' A B q
theorem mem_pinter (A B : PathSet) (q : Path) : q ∈ PathSet.inter A B ↔ q ∈ A ∧ q ∈ B :=
  FSet.mem_inter' A B q
theorem mem_pdiff (A B : PathSet) (q : Path) : q ∈ PathSet.diff A B ↔ q ∈ A ∧ q ∉ B :=
  FSet.mem_diff' A B q

/-! ## Emptiness -/

theorem isEmpty_iff (S : PathSet) : S.IsEmpty ↔ ∀ q, q ∉ S := FSet.isEmpty_iff' S

/-- A set without the empty path is empty iff its members and its children are. -/
theorem isEmpty_split (S : PathSet) (hne : [] ∉ S) :
    S.IsEmpty ↔ (∀ e, e ∉ S.tops) ∧ S.deep.IsEmpty := by
  rw [isEmpty_iff, isEmpty_iff]
  simp only [mem_tops, mem_deep]
  constructor
  · intro h; exact ⟨fun e => h [e], fun q hq => h q hq.1⟩
  · rintro ⟨h1, h2⟩ q hq
    match q with
    | [] => exact hne hq
    | [e] => exact h1 e hq
    | e :: e' :: r => exact h2 _ ⟨hq, by simp⟩

/-- A well-formed node list's paths are empty iff it has no node. -/
theorem nl_isEmpty (l : NL) (hl : NLok l) (D : PathSet) (hD : ∀ q, q ∈ D ↔ q ∈ nlPaths l) :
    D.IsEmpty ↔ l = [] := by
  rw [isEmpty_iff]
  constructor
  · intro h
    match l, hl with
    | [], _ => rfl
    | (k, S) :: l', hl =>
      obtain ⟨-, ⟨r, hr⟩, -⟩ := hl.2 k S (List.mem_cons_self ..)
      exact absurd ((hD _).2 ((mem_nlPaths _ _).2 ⟨k, S, r, List.mem_cons_self .., hr, rfl⟩))
        (h (k :: r))
  · rintro rfl q hq; exact mem_nlPaths_nil q ((hD q).1 hq)

end fpC

/-! ## The representation, viewed as members and node lists -/

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace fpC

theorem trieRep_mk_eq (p : Loc) (ms : List PE) (cs : List (PE × Trie)) :
    trieRep (GF := GF) p (.mk ms cs) = iprop(∃ (v : fieldpath.Set') (es : List fieldpath.PathElement)
      (ns : List fieldpath.setNode),
      p ↦□ v ∗ v.Members'.members' ↦*{DFrac.discard} es ∗ isPEL es ms ∗
      v.Children'.members' ↦*{DFrac.discard} ns ∗ trieRepC ns cs) := by
  simp only [trieRep]

theorem trieRepC_nil_eq : trieRepC (GF := GF) [] [] = iprop(True) := by simp only [trieRepC]

theorem trieRepC_cons_eq (n : fieldpath.setNode) (ns : List fieldpath.setNode) (pe : PE) (t : Trie)
    (cs : List (PE × Trie)) :
    trieRepC (GF := GF) (n :: ns) ((pe, t) :: cs) =
      iprop(isPE n.pathElement' pe ∗ trieRep n.set' t ∗ trieRepC ns cs) := by
  simp only [trieRepC]

/-- A `SetNodeMap`'s nodes as (path element, set) pairs: each node's element and `isSet`. -/
def nodesL : List fieldpath.setNode → NL → IProp GF
  | [], [] => iprop(True)
  | n :: ns, (k, S) :: l => iprop(isPE n.pathElement' k ∗ isSet n.set' S ∗ nodesL ns l)
  | _, _ => iprop(False)

instance nodesL_pers : (ns : List fieldpath.setNode) → (l : NL) → Persistent (nodesL (GF := GF) ns l)
  | [], [] => by unfold nodesL; infer_instance
  | [], _ :: _ => by unfold nodesL; infer_instance
  | _ :: _, [] => by unfold nodesL; infer_instance
  | n :: ns, (k, S) :: l => by
      unfold nodesL
      have := nodesL_pers ns l
      infer_instance

theorem nodesL_cons_eq (n : fieldpath.setNode) (ns : List fieldpath.setNode) (k : PE) (S : PathSet)
    (l : NL) : nodesL (GF := GF) (n :: ns) ((k, S) :: l) =
      iprop(isPE n.pathElement' k ∗ isSet n.set' S ∗ nodesL ns l) := by
  simp only [nodesL]

theorem nodesL_nil_eq : nodesL (GF := GF) [] [] = iprop(True) := by simp only [nodesL]

theorem nodesL_length : ∀ (ns : List fieldpath.setNode) (l : NL),
    nodesL (GF := GF) ns l ⊢ ⌜ns.length = l.length⌝
  | [], [] => by iintro _; ipureintro; rfl
  | [], _ :: _ => by unfold nodesL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold nodesL; iintro %h; exact h.elim
  | n :: ns, (k, S) :: l => by
    rw [nodesL_cons_eq]; iintro ⟨-, -, H⟩
    ihave %h := nodesL_length ns l $$ H
    ipureintro; simp [h]

theorem nodesL_wf : ∀ (ns : List fieldpath.setNode) (l : NL),
    nodesL (GF := GF) ns l ⊢ ⌜∀ k S, (k, S) ∈ l → k.wf = true⌝
  | [], [] => by iintro _; ipureintro; simp
  | [], _ :: _ => by unfold nodesL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold nodesL; iintro %h; exact h.elim
  | n :: ns, (k, S) :: l => by
    rw [nodesL_cons_eq]; iintro ⟨He, -, H⟩
    ihave %h1 := fpL.isPE_wf' _ _ $$ He
    ihave %h2 := nodesL_wf ns l $$ H
    ipureintro
    intro k' S' hk
    rcases List.mem_cons.1 hk with h | h
    · cases h; exact h1
    · exact h2 k' S' h

theorem nodesL_app : ∀ (ns ns' : List fieldpath.setNode) (l l' : NL), ns.length = l.length →
    (nodesL (GF := GF) (ns ++ ns') (l ++ l') ⊣⊢ nodesL ns l ∗ nodesL ns' l')
  | [], ns', [], l', _ => by
    simp only [List.nil_append, nodesL_nil_eq]
    exact ⟨by iintro H; iframe H, by iintro ⟨-, H⟩; iexact H⟩
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | n :: ns, ns', (k, S) :: l, l', h => by
    simp only [List.cons_append]
    have ih := nodesL_app ns ns' l l' (by simpa using h)
    simp only [nodesL_cons_eq]
    constructor
    · iintro ⟨He, Hs, H⟩
      icases ih.1 $$ H with ⟨H1, H2⟩
      iframe
    · iintro ⟨⟨He, Hs, H1⟩, H2⟩
      iframe
      iapply ih.2; iframe

theorem nodesL_lookup : ∀ (ns : List fieldpath.setNode) (l : NL) (k : Nat) (n : fieldpath.setNode),
    ns[k]? = some n → nodesL (GF := GF) ns l ⊢
      ∃ pe S, ⌜l[k]? = some (pe, S)⌝ ∗ isPE n.pathElement' pe ∗ isSet n.set' S
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold nodesL; iintro %h; exact h.elim
  | n' :: ns, (k', S') :: l, 0, n, h => by
    simp at h; subst h
    rw [nodesL_cons_eq]; iintro ⟨He, Hs, -⟩; iexists k', S'; iframe; ipureintro; rfl
  | n' :: ns, (k', S') :: l, k + 1, n, h => by
    simp at h
    rw [nodesL_cons_eq]; iintro ⟨-, -, H⟩
    simp only [List.getElem?_cons_succ]
    iapply nodesL_lookup ns l k n h; iexact H

theorem trieRepC_nodesL : ∀ (ns : List fieldpath.setNode) (cs : List (PE × Trie)),
    Trie.CanonicalC cs → trieRepC (GF := GF) ns cs ⊢ nodesL ns (nlOf cs)
  | [], [], _ => by
    rw [trieRepC_nil_eq, show nlOf [] = [] from rfl, nodesL_nil_eq]
  | [], _ :: _, _ => by unfold trieRepC; iintro %h; exact h.elim
  | _ :: _, [], _ => by unfold trieRepC; iintro %h; exact h.elim
  | n :: ns, (pe, t) :: cs, hc => by
    simp only [Trie.CanonicalC] at hc
    rw [trieRepC_cons_eq, show nlOf ((pe, t) :: cs) = (pe, tset t) :: nlOf cs from rfl,
      nodesL_cons_eq]
    iintro ⟨He, Ht, H⟩
    iframe He
    isplitl [Ht]
    · unfold isSet; iexists t; iframe; ipureintro
      exact ⟨hc.1, fun q => (mem_tset t q).symm⟩
    · iapply trieRepC_nodesL ns cs hc.2.2; iexact H

theorem nodesL_trieRepC : ∀ (ns : List fieldpath.setNode) (l : NL),
    (∀ k S, (k, S) ∈ l → ∃ q, q ∈ S) →
    nodesL (GF := GF) ns l ⊢ ∃ cs, trieRepC ns cs ∗ ⌜Trie.CanonicalC cs ∧ nlOf cs = l⌝
  | [], [], _ => by
    iintro _; iexists []; rw [trieRepC_nil_eq]; isplit
    · itrivial
    · ipureintro; exact ⟨trivial, rfl⟩
  | [], _ :: _, _ => by unfold nodesL; iintro %h; exact h.elim
  | _ :: _, [], _ => by unfold nodesL; iintro %h; exact h.elim
  | n :: ns, (k, S) :: l, hne => by
    rw [nodesL_cons_eq]
    iintro ⟨He, Hs, H⟩
    icases nodesL_trieRepC ns l (fun k' S' h => hne k' S' (List.mem_cons_of_mem _ h)) $$ H
      with ⟨%cs, Hc, %hc⟩
    unfold isSet
    icases Hs with ⟨%t, %ht, Ht⟩
    iexists (k, t) :: cs
    rw [trieRepC_cons_eq]
    iframe
    ipureintro
    obtain ⟨q, hq⟩ := hne k S (List.mem_cons_self ..)
    refine ⟨⟨ht.1, ⟨q, (ht.2 q).2 hq⟩, hc.1⟩, ?_⟩
    simp only [nlOf, List.map_cons]
    have e : tset t = S := FSet.ext' (fun q => by rw [mem_tset]; exact ht.2 q)
    rw [e]
    simp only [nlOf] at hc
    rw [hc.2]

/-- **The node-list view of a `SetNodeMap`.** -/
theorem isNodesV_view (m : fieldpath.SetNodeMap) (D : PathSet) :
    isNodesV (GF := GF) m D ⊣⊢ ∃ ns l, m.members' ↦*{DFrac.discard} ns ∗ nodesL ns l ∗
      ⌜NLok l ∧ ∀ q, q ∈ D ↔ q ∈ nlPaths l⌝ := by
  constructor
  · unfold isNodesV
    iintro ⟨%ns, %cs, Hm, Hc, %h⟩
    ihave #Hl := trieRepC_nodesL ns cs h.2.1 $$ Hc
    ihave %hw := nodesL_wf ns (nlOf cs) $$ Hl
    iexists ns, nlOf cs
    iframe
    isplit
    · iexact Hl
    ipureintro
    refine ⟨⟨?_, ?_⟩, fun q => by rw [← h.2.2 q, pathsC_nlOf]⟩
    · rw [nlOf_keys]; exact h.1
    · intro k S hk
      refine ⟨hw k S hk, ?_⟩
      simp only [nlOf, List.mem_map] at hk
      obtain ⟨⟨e, t⟩, hm, he⟩ := hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨-, q, hq⟩ := canonicalC_mem cs e t h.2.1 hm
      exact ⟨tset_nonempty_of _ _ hq, fun hn => paths_ne_nil t ((mem_tset t []).1 hn)⟩
  · unfold isNodesV
    iintro ⟨%ns, %l, Hm, #Hl, %h⟩
    icases nodesL_trieRepC ns l (fun k S hk => (h.1.2 k S hk).2.1) $$ Hl with ⟨%cs, Hc, %hc⟩
    iexists ns, cs
    iframe
    isplit
    · iexact Hc
    ipureintro
    refine ⟨?_, hc.1, fun q => ?_⟩
    · rw [← nlOf_keys, hc.2]; exact h.1.1
    · rw [pathsC_nlOf, hc.2, h.2 q]

/-- **The members/children view of a set.** -/
theorem isSet_view (p : Loc) (S : PathSet) :
    isSet (GF := GF) p S ⊣⊢ ∃ v : fieldpath.Set', p ↦□ v ∗
      isPESetV v.Members' DFrac.discard S.tops ∗ isNodesV v.Children' S.deep ∗ ⌜[] ∉ S⌝ := by
  constructor
  · unfold isSet
    iintro ⟨%t, %ht, Ht⟩
    obtain ⟨ms, cs⟩ := t
    rw [trieRep_mk_eq]
    icases Ht with ⟨%v, %es, %ns, Hp, Hes, Hms, Hns, Hcs⟩
    simp only [Trie.Canonical] at ht
    iexists v
    iframe Hp
    isplitl [Hes Hms]
    · unfold isPESetV
      iexists es, ms
      iframe
      ipureintro
      refine ⟨ht.1.1, FSet.ext' (fun e => ?_)⟩
      rw [FSet.mem_ofList', PathSet_mem_tops_law_holds, ← ht.2, paths_mk]
      constructor
      · intro h; exact Or.inl ⟨e, rfl, h⟩
      · rintro (⟨e', he, h⟩ | h)
        · cases he; exact h
        · exact absurd h (pathsC_single cs e)
    isplitl [Hns Hcs]
    · unfold isNodesV
      iexists ns, cs
      iframe
      ipureintro
      refine ⟨ht.1.2.1, ht.1.2.2, fun q => ?_⟩
      rw [PathSet_mem_deep_law_holds, ← ht.2, paths_mk]
      constructor
      · intro h; exact ⟨Or.inr h, pathsC_len cs q h⟩
      · rintro ⟨⟨e, rfl, -⟩ | h, hl⟩
        · simp at hl
        · exact h
    · ipureintro
      intro h
      have := (ht.2 []).2 h
      rw [paths_mk] at this
      rcases this with ⟨e, he, -⟩ | h
      · cases he
      · exact pathsC_ne_nil cs h
  · iintro ⟨%v, #Hp, Hm, Hc, %hne⟩
    unfold isPESetV isNodesV
    icases Hm with ⟨%es, %xs, Hes, Hxs, %hx⟩
    icases Hc with ⟨%ns, %cs, Hns, Hcs, %hc⟩
    unfold isSet
    iexists .mk xs cs
    isplit
    · ipureintro
      refine ⟨⟨hx.1, hc.1, hc.2.1⟩, fun q => ?_⟩
      rw [paths_mk]
      match q with
      | [] =>
        constructor
        · rintro (⟨e, he, -⟩ | h)
          · cases he
          · exact absurd h (pathsC_ne_nil cs)
        · intro h; exact absurd h hne
      | [e] =>
        rw [← PathSet_mem_tops_law_holds, ← hx.2, FSet.mem_ofList']
        constructor
        · rintro (⟨e', he, h⟩ | h)
          · cases he; exact h
          · exact absurd h (pathsC_single cs e)
        · intro h; exact Or.inl ⟨e, rfl, h⟩
      | e :: e' :: r =>
        rw [hc.2.2, PathSet_mem_deep_law_holds]
        simp
    · rw [trieRep_mk_eq]
      iexists v, es, ns
      iframe
      iframe #

end fpC
end views

end smd
end EtcdGrove
end Perennial
