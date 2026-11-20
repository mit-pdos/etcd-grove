/-
**The facts behind `Set`/`SetNodeMap.EnsureNamedFieldsAreMembers`' bodies**: the children's part
of `ensureNamedOpt` (only deep paths matter), a set's members and node counts bounded by its
cardinality, and the child type Go computes.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsTrie
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsNamed
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet
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

namespace fpE

theorem mem_under' (S : PathSet) (e : PE) (q : Path) : q ∈ S.under e ↔ q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_under_law_holds S e q
theorem mem_deep' (S : PathSet) (q : Path) : q ∈ S.deep ↔ q ∈ S ∧ 2 ≤ q.length :=
  PathSet_mem_deep_law_holds S q
theorem mem_tops' (S : PathSet) (e : PE) : e ∈ S.tops ↔ [e] ∈ S := PathSet_mem_tops_law_holds S e
theorem mem_heads' (S : PathSet) (e : PE) : e ∈ S.heads ↔ ∃ q, q ≠ [] ∧ (e :: q) ∈ S :=
  PathSet_mem_heads_law_holds S e

theorem ens_under (S : Schema) (ty : Option TypeRef) (s : PathSet) (e : PE) :
    (ensureNamedOpt S ty s).under e = ensureNamedOpt S (childType S ty e) (s.under e) :=
  ensureNamedOpt_under_law_holds S ty s e

/-- A path of two or more elements, by its head and rest. -/
theorem mem_deep_cons (A : PathSet) (e : PE) (r : Path) :
    (e :: r) ∈ A.deep ↔ r ∈ A.under e := by
  rw [mem_deep', mem_under']
  constructor
  · rintro ⟨h, hl⟩; refine ⟨?_, h⟩; rintro rfl; simp at hl
  · rintro ⟨hr, h⟩; refine ⟨h, ?_⟩
    match r, hr with
    | _ :: _, _ => simp

theorem under_deep (A : PathSet) (e : PE) : A.deep.under e = A.under e := by
  apply FSet.ext'; intro q
  rw [mem_under', mem_under', mem_deep']
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨h1, h2, ?_⟩
    match q, h1 with
    | _ :: _, _ => simp

theorem deep_ext {A B : PathSet} (h : ∀ e, A.under e = B.under e) : A.deep = B.deep := by
  apply FSet.ext'; intro q
  match q with
  | [] => rw [mem_deep', mem_deep']; simp
  | e :: r => rw [mem_deep_cons, mem_deep_cons, h e]

/-- **Only the deep paths reach the children's part.** -/
theorem ens_deep (S : Schema) (ty : Option TypeRef) (s : PathSet) :
    (ensureNamedOpt S ty s).deep = (ensureNamedOpt S ty s.deep).deep := by
  apply deep_ext; intro e
  rw [ens_under, ens_under, under_deep]

theorem ens_nil (S : Schema) (ty : Option TypeRef) (s : PathSet) (h : [] ∉ s) :
    [] ∉ ensureNamedOpt S ty s := by
  rw [fpD.mem_ensureNamedOpt]
  rintro (h' | ⟨p, -, hq⟩)
  · exact h h'
  · exact fpD.namedAlong_ne S ty p [] hq rfl

theorem ens_sub (S : Schema) (ty : Option TypeRef) (s : PathSet) (q : Path) (h : q ∈ s) :
    q ∈ ensureNamedOpt S ty s := (fpD.mem_ensureNamedOpt S ty s q).2 (Or.inl h)

/-! ## The child type Go computes -/

theorem resolveRef_bind (S : Schema) (ty : Option TypeRef) :
    ty.bind (fun t => S.find t.name) = S.resolveRef ty := by
  cases ty <;> rfl

theorem childType_map {S : Schema} {ty : Option TypeRef} {fs : List (GoString × TypeRef)}
    {e : Option TypeRef} {rel : ElemRel} (h : S.resolveRef ty = some (.map fs e rel)) (n : GoString) :
    childType S ty (.field n) = fieldType fs e n := by
  unfold childType; rw [resolveRef_bind, h]

theorem childType_list {S : Schema} {ty : Option TypeRef} {e : TypeRef} {rel : ElemRel}
    {ks : List GoString} (h : S.resolveRef ty = some (.list e rel ks)) (fl : FieldList) :
    childType S ty (.key fl) = some e := by
  unfold childType; rw [resolveRef_bind, h]

theorem childType_other {S : Schema} {ty : Option TypeRef} {pe : PE}
    (h1 : ∀ n fs e rel, ¬ (pe = .field n ∧ S.resolveRef ty = some (.map fs e rel)))
    (h2 : ∀ fl e rel ks, ¬ (pe = .key fl ∧ S.resolveRef ty = some (.list e rel ks))) :
    childType S ty pe = none := by
  unfold childType; rw [resolveRef_bind]
  split
  · next fs e rel n h => exact absurd ⟨rfl, h⟩ (h1 n fs e rel)
  · next e rel ks fl h => exact absurd ⟨rfl, h⟩ (h2 fl e rel ks)
  · rfl

/-- A child of `SetNodeMap.EnsureNamedFieldsAreMembers`' result: the node's set with its named
fields made members, at the child's type. -/
def ensF (S : Schema) (ty : Option TypeRef) (p : PE × PathSet) : PE × PathSet :=
  (p.1, ensureNamedOpt S (childType S ty p.1) p.2)

/-- The children's node list keeps the keys. -/
theorem ensF_keys (S : Schema) (ty : Option TypeRef) (l : fpC.NL) :
    fpC.keys (l.map (ensF S ty)) = fpC.keys l := by
  simp [fpC.keys, ensF, Function.comp_def]

theorem ens_nlok (S : Schema) (ty : Option TypeRef) {l : fpC.NL} (h : fpC.NLok l) :
    fpC.NLok (l.map (ensF S ty)) := by
  refine ⟨?_, ?_⟩
  · have := ensF_keys S ty l
    simp only [fpC.keys] at this
    rw [this]; exact h.1
  · intro k S' hm
    obtain ⟨⟨k0, S0⟩, hm0, he⟩ := List.mem_map.1 hm
    simp only [ensF, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hw, ⟨q, hq⟩, hn⟩ := h.2 k0 S0 hm0
    exact ⟨hw, ⟨q, ens_sub _ _ _ _ hq⟩, ens_nil _ _ _ hn⟩

theorem ens_empty (S : Schema) (ty : Option TypeRef) (A : PathSet) (h : ∀ q, q ∉ A) (q : Path) :
    q ∉ ensureNamedOpt S ty A := by
  rw [fpD.mem_ensureNamedOpt]
  rintro (hq | ⟨p, hp, -⟩)
  · exact h q hq
  · exact h p hp

/-- **The children's paths**: the deep paths of the whole result. -/
theorem ens_nlPaths (S : Schema) (ty : Option TypeRef) {l : fpC.NL} (hl : fpC.NLok l) (D : PathSet)
    (hD : ∀ q, q ∈ D ↔ q ∈ fpC.nlPaths l) (q : Path) :
    q ∈ (ensureNamedOpt S ty D).deep ↔ q ∈ fpC.nlPaths (l.map (ensF S ty)) := by
  have hl' := ens_nlok S ty hl
  match q with
  | [] =>
    rw [mem_deep']
    constructor
    · rintro ⟨-, h⟩; simp at h
    · intro h
      obtain ⟨k, r, he, -⟩ := fpC.nl_heads _ h
      cases he
  | e :: r =>
    rw [mem_deep_cons, ens_under]
    by_cases hk : e ∈ fpC.keys l
    · obtain ⟨⟨k0, S0⟩, hm0, he⟩ := List.mem_map.1 hk
      simp only at he; subst he
      have hU : D.under k0 = S0 := by
        apply FSet.ext'; intro x
        rw [mem_under', hD, fpC.nl_col hl hm0]
        constructor
        · exact fun h => h.2
        · intro h; refine ⟨?_, h⟩; rintro rfl; exact (hl.2 k0 S0 hm0).2.2 h
      rw [hU, fpC.nl_col hl' (List.mem_map_of_mem (f := ensF S ty) hm0)]
    · have hU : ∀ x, x ∉ D.under e := by
        intro x hx
        rw [mem_under', hD] at hx
        exact fpC.nl_nokey hk x hx.2
      constructor
      · intro h; exact absurd h (ens_empty _ _ _ hU r)
      · intro h
        rw [← ensF_keys S ty l] at hk
        exact absurd h (fpC.nl_nokey hk r)

/-! ## The members part (`Set.EnsureNamedFieldsAreMembers`' loop) -/

/-- A child key Go makes a member: a declared field of the map type at `ty`. -/
def namedB (S : Schema) (ty : Option TypeRef) (pe : PE) : Bool :=
  match pe, S.resolveRef ty with
  | .field n, some (.map fs _ _) => (lookupKV n fs).isSome
  | _, _ => false

theorem namedB_map {S : Schema} {ty : Option TypeRef} {fs : List (GoString × TypeRef)}
    {e : Option TypeRef} {rel : ElemRel} (h : S.resolveRef ty = some (.map fs e rel)) (n : GoString) :
    namedB S ty (.field n) = (lookupKV n fs).isSome := by
  unfold namedB; rw [h]

theorem namedB_other {S : Schema} {ty : Option TypeRef} {pe : PE}
    (h1 : ∀ n fs e rel, ¬ (pe = .field n ∧ S.resolveRef ty = some (.map fs e rel))) :
    namedB S ty pe = false := by
  unfold namedB
  split
  · next n fs e rel h => exact absurd ⟨rfl, h⟩ (h1 n fs e rel)
  · rfl

theorem namedB_iff (S : Schema) (ty : Option TypeRef) (pe : PE) :
    namedB S ty pe = true ↔ ∃ n fs el rel, pe = .field n ∧
      ty.bind (fun t => S.find t.name) = some (.map fs el rel) ∧ (lookupKV n fs).isSome := by
  rw [resolveRef_bind]
  constructor
  · intro h
    unfold namedB at h
    split at h
    · next n fs e rel hr => exact ⟨n, fs, e, rel, rfl, hr, h⟩
    · simp at h
  · rintro ⟨n, fs, el, rel, rfl, hr, hs⟩
    rw [namedB_map hr]; exact hs

/-- **The members of the result**: `s`'s and the named fields among its children's keys. -/
theorem ens_tops (S : Schema) (ty : Option TypeRef) (s : PathSet) {l : fpC.NL} (hl : fpC.NLok l)
    (hD : ∀ q, q ∈ s.deep ↔ q ∈ fpC.nlPaths l) :
    (ensureNamedOpt S ty s).tops =
      FSet.union s.tops (FSet.ofList ((fpC.keys l).filter (namedB S ty))) := by
  apply FSet.ext'; intro e
  rw [ensureNamedOpt_tops_law_holds, FSet.mem_union', FSet.mem_ofList', List.mem_filter,
    namedB_iff]
  have hh : e ∈ s.heads ↔ e ∈ fpC.keys l := by
    rw [mem_heads', fpK.nl_key_iff hl]
    constructor
    · rintro ⟨q, hq, hm⟩
      refine ⟨q, (hD _).1 ((mem_deep' _ _).2 ⟨hm, ?_⟩)⟩
      match q, hq with
      | _ :: _, _ => simp
    · rintro ⟨r, hr⟩
      obtain ⟨hm, hlen⟩ := (mem_deep' _ _).1 ((hD _).2 hr)
      refine ⟨r, ?_, hm⟩
      rintro rfl; simp at hlen
  rw [hh]

theorem card_pos' {S : PathSet} {q : Path} (h : q ∈ S) : 1 ≤ S.card := by
  have : (FSet.ofList [q]).card ≤ S.card := FSet.card_le_of_subset _ _ (fun x hx => by
    rw [FSet.mem_ofList', List.mem_singleton] at hx; subst hx; exact h)
  have h1 : (FSet.ofList [q]).card = 1 := rfl
  omega

/-- A well-formed node list counts at most its paths. -/
theorem nl_length_le (l : fpC.NL) (hl : fpC.NLok l) : ∀ i, i ≤ l.length →
    i ≤ (fpC.nlPaths (l.take i)).card
  | 0, _ => Nat.zero_le _
  | i + 1, h => by
    have hnd : (fpC.keys l).Nodup := fpC.sorted_nodup _ (fpC.nlok_wf hl) hl.1
    have hi : i < l.length := h
    rw [fpK.nl_card_take l i hi hnd]
    have ih := nl_length_le l hl i (Nat.le_of_lt hi)
    obtain ⟨-, ⟨q, hq⟩, -⟩ := hl.2 l[i].1 l[i].2 (List.getElem_mem hi)
    have := card_pos' hq
    omega

theorem members_step_in (S : Schema) (ty : Option TypeRef) (T : FSet PE) (ks : List PE) (pe : PE)
    (h : namedB S ty pe = true) :
    FSet.union (FSet.union T (FSet.ofList (ks.filter (namedB S ty)))) (FSet.ofList [pe]) =
      FSet.union T (FSet.ofList ((ks ++ [pe]).filter (namedB S ty))) := by
  apply FSet.ext'; intro x
  simp only [FSet.mem_union', FSet.mem_ofList', List.filter_append, List.filter_cons, h,
    ↓reduceIte, List.filter_nil, List.mem_append, List.mem_singleton]
  exact or_assoc

theorem members_step_out (S : Schema) (ty : Option TypeRef) (T : FSet PE) (ks : List PE) (pe : PE)
    (h : namedB S ty pe = false) :
    FSet.union T (FSet.ofList (ks.filter (namedB S ty))) =
      FSet.union T (FSet.ofList ((ks ++ [pe]).filter (namedB S ty))) := by
  rw [List.filter_append, List.filter_cons, h]
  simp

theorem card_ofList_le (l : List PE) : (FSet.ofList l).card ≤ l.length :=
  fpN.dedupL_length_le l

end fpE

section reps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A field's path element has no key.** Not provable from the frozen `isPE (.field n)`, which
pins only `FieldName` (`Defs.lean`): a `PathElement` with both `FieldName` and `Key` set satisfies
it, and `SetNodeMap.EnsureNamedFieldsAreMembers` then takes the `else if pe.Key != nil` branch
under a list type (the child at the list's element type, where its spec says `childType = none`).
Every `PathElement` SMD builds has exactly one field set; the smallest fix is to add
`⌜e.Key' = null⌝` to `isPE`'s `.field` case (its introduction, `PathElement{FieldName: &n}`, has a
nil `Key`). Reported (agent C4, 2026-11-20). -/
theorem fpE.isPE_field_key (e : fieldpath.PathElement) (n : GoString) :
    isPE (GF := GF) e (.field n) ⊢ ⌜e.Key' = null⌝ := by
  sorry

/-- A path element's field name, set exactly for a field. -/
theorem fpE.isPE_field (e : fieldpath.PathElement) (n : GoString) :
    isPE (GF := GF) e (.field n) ⊢ e.FieldName' ↦□ n := by
  unfold isPE; iintro H; iexact H

/-- A path element's field name is nil exactly when it is not a field. -/
theorem fpE.isPE_fieldName_ptr (e : fieldpath.PathElement) (pe : PE) :
    isPE (GF := GF) e pe ⊢ ⌜e.FieldName' = null ↔ ∀ n, pe ≠ .field n⌝ := by
  rcases pe with n | fl | x | i <;> unfold isPE
  · iintro #H
    ihave %hn := typedPointsto_not_null $$ H
    ipureintro
    simp [hn]
  all_goals
    iintro ⟨%h, -⟩
    ipureintro
    simp [h.1]

/-- Which of a path element's pointers are nil, by its kind. -/
theorem fpE.isPE_ptrs (e : fieldpath.PathElement) (pe : PE) :
    isPE (GF := GF) e pe ⊢
      ⌜(e.FieldName' = null ↔ ∀ n, pe ≠ .field n) ∧ (e.Key' = null ↔ ∀ fl, pe ≠ .key fl)⌝ := by
  rcases pe with n | fl | x | i
  · iintro #H
    ihave %hk := fpE.isPE_field_key e n $$ H
    unfold isPE
    ihave %hn := typedPointsto_not_null $$ H
    ipureintro
    simp [hn, hk]
  · unfold isPE
    iintro ⟨%h, %s, #Hk, -⟩
    ihave %hn := typedPointsto_not_null $$ Hk
    ipureintro
    simp [h.1, hn]
  · unfold isPE
    iintro ⟨%h, -⟩
    ipureintro
    simp [h.1, h.2.1]
  · unfold isPE
    iintro ⟨%h, -⟩
    ipureintro
    simp [h.1, h.2.1]

/-- **A set's members copied** into a fresh owned slice (`append(make(…), s.Members.members...)`). -/
theorem fpE.isPESetV_copy (v : fieldpath.PathElementSet) (T : FSet PE) :
    isPESetV (GF := GF) v DFrac.discard T ⊢ ∃ es : List fieldpath.PathElement,
      v.members' ↦*{DFrac.discard} es ∗
      □ (∀ sl : GoSlice, sl ↦* es -∗ ownSliceCap fieldpath.PathElement sl (DFrac.own 1) -∗
        ownPESetV (fieldpath.PathElementSet.mk sl) T) := by
  unfold isPESetV
  iintro ⟨%es, %xs, #Hs, #Hx, %h⟩
  iexists es
  isplit
  · iexact Hs
  imodintro
  iintro %sl Hsl Hc
  unfold ownPESetV
  iexists es, xs
  iframe
  isplit
  · iexact Hx
  ipureintro; exact h

end reps

end smd
end EtcdGrove
end Perennial
