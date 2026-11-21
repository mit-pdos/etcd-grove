/-
**The pure facts of `Updater.Apply`'s glue** (`merge/Updater__Apply.lean`): `prune`'s and
`update`'s premises from `Apply`'s (the one-version and `keysWithItems` premise on the managers,
D9's `inputsSmall`, the objects' conformance).
Prove phase (2026-11-21).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsM1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace Glue

/-! ## Trie nodes -/

theorem mem_nePrefixes_append {q p : Path} (r : Path) (h : q ∈ Path.nePrefixes p) :
    q ∈ Path.nePrefixes (p ++ r) := by
  unfold Path.nePrefixes at h ⊢
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
  rw [List.mem_range] at hk
  refine List.mem_map.2 ⟨k, ?_, ?_⟩
  · rw [List.mem_range, List.length_append]; omega
  · rw [List.take_append_of_le_length (by omega)]

/-- Reconciling adds no trie node (its paths are the set's, or prefixes of them). -/
theorem reconcile_nodes_sub (S : Schema) (t : TypeRef) (s : PathSet) (q : Path)
    (hq : q ∈ (reconcile S t s).nodes) : q ∈ s.nodes := by
  unfold PathSet.nodes at hq ⊢
  rw [FSet_mem_bind_law_holds] at hq ⊢
  obtain ⟨x, hx, hqx⟩ := hq
  rcases (reconcile_mem_law_holds S t s x).1 hx with ⟨hxs, -⟩ | hxa
  · exact ⟨x, hxs, hqx⟩
  · obtain ⟨-, ⟨r, -, hr⟩, -⟩ := (atomicNodes_mem_law_holds S t s x).1 hxa
    exact ⟨x ++ r, hr, mem_nePrefixes_append r hqx⟩

theorem reconcile_nodes_le (S : Schema) (t : TypeRef) (s : PathSet) :
    (reconcile S t s).nodes.card ≤ s.nodes.card :=
  FSet.card_le_of_subset _ _ (reconcile_nodes_sub S t s)

/-! ## `keysWithItems` of the sets `Apply` hands to `prune` -/

theorem typeAlong_none (S : Schema) : ∀ q : Path, typeAlong S none q = none
  | [] => rfl
  | _ :: q => by simp only [typeAlong, childType, Option.bind_none]; exact typeAlong_none S q

/-- Where both are defined, the type along a path (`EnsureNamedFieldsAreMembers`' descent) is
the reconciling walker's. -/
theorem typeAlong_reconAt (S : Schema) : ∀ (q : Path) (t x y : TypeRef),
    typeAlong S (some t) q = some x → reconAt S t q = some y → x = y
  | [], t, x, y, h1, h2 => by
    simp only [typeAlong, reconAt, Option.some.injEq] at h1 h2; subst h1 h2; rfl
  | pe :: q, t, x, y, h1, h2 => by
    simp only [typeAlong] at h1
    simp only [reconAt] at h2
    split at h2
    · split at h2
      · rename_i t' ht'
        cases hc : childType S (some t) pe with
        | none => rw [hc, typeAlong_none] at h1; cases h1
        | some c =>
          rw [hc] at h1
          have : c = t' := by
            unfold childType at hc
            unfold reconChild at ht'
            simp only [Option.bind_some] at hc
            split at hc
            · rename_i fs e rel n hf
              rw [hf] at ht'; simp only at ht'
              rw [ht'] at hc; cases hc; rfl
            · rename_i e rel ks k hf
              rw [hf] at ht'; simp only [Option.some.injEq] at ht' hc; subst ht' hc; rfl
            · cases hc
          subst this
          exact typeAlong_reconAt S q c x y h1 h2
      · cases h2
    · cases h2

theorem atomic_ne_granular (S : Schema) (t : TypeRef) (q : Path) (t' : TypeRef)
    (hr : reconAt S t q = some t') (ha : isAtomicT S t' = true)
    (hm : ∃ fs e rel, (typeAlong S (some t) q).bind (fun t => S.find t.name) =
      some (.map fs e rel) ∧ rel ≠ .atomic) : False := by
  obtain ⟨fs, e, rel, hf, hrel⟩ := hm
  cases hx : typeAlong S (some t) q with
  | none => rw [hx] at hf; cases hf
  | some x =>
    rw [hx] at hf
    have := typeAlong_reconAt S q t x t' hx hr
    subst this
    simp only [Option.bind_some] at hf
    unfold isAtomicT at ha
    rw [hf] at ha
    cases rel <;> simp_all

/-- Reconciling keeps `keysWithItems`. -/
theorem kwi_reconcile (S : Schema) (t : TypeRef) (s : PathSet)
    (h : keysWithItems S t s) : keysWithItems S t (reconcile S t s) := by
  -- an atomic node has a path of `s` strictly below it
  have hbelow : ∀ q, q ∈ atomicNodes S t s → ∃ r, r ≠ [] ∧ (q ++ r) ∈ s := fun q hq =>
    ((atomicNodes_mem_law_holds S t s q).1 hq).2.1
  -- no atomic node is at or below a key field (clause 3)
  have hkey : ∀ p fl n v r, (n, v) ∈ fl →
      (p ++ [.key fl, .field n] ++ r) ∉ atomicNodes S t s := by
    intro p fl n v r hn ha
    obtain ⟨r', hr', hs⟩ := hbelow _ ha
    refine (h p fl).2.2 n v (r ++ r') hn (fun h0 => hr' (List.append_eq_nil_iff.1 h0).2) ?_
    rw [← List.append_assoc]; exact hs
  -- a path of `s` not covered by an atomic node
  have hcov : ∀ q q', q ++ q' ∈ s → (¬ ∃ a, a ∈ atomicNodes S t s ∧ a <+: q ++ q') →
      ¬ ∃ a, a ∈ atomicNodes S t s ∧ a <+: q := by
    intro q q' _ hn ⟨a, ha, hp⟩
    exact hn ⟨a, ha, hp.trans (List.prefix_append q q')⟩
  intro p fl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, v, hn, hm⟩
    rcases (reconcile_mem_law_holds S t s _).1 hm with ⟨hs, hnc⟩ | ha
    · apply (reconcile_mem_law_holds S t s _).2
      left
      refine ⟨(h p fl).1 ⟨n, v, hn, hs⟩, ?_⟩
      exact hcov (p ++ [.key fl]) [.field n] (by simpa using hs) (by simpa using hnc)
    · exact absurd (by simpa using ha) (hkey p fl n v [] hn)
  · intro hm hty n v hn
    rcases (reconcile_mem_law_holds S t s _).1 hm with ⟨hs, hnc⟩ | ha
    · have hs' := (h p fl).2.1 hs hty n v hn
      apply (reconcile_mem_law_holds S t s _).2
      left
      refine ⟨hs', ?_⟩
      rintro ⟨a, ha, hpre⟩
      obtain ⟨r, hr⟩ := hpre
      -- `a` is a prefix of the item, or the key field's path itself
      rcases List.eq_nil_or_concat r with rfl | ⟨r0, x, rfl⟩
      · simp only [List.append_nil] at hr; subst hr
        exact hkey p fl n v [] hn (by simpa using ha)
      · have : a ++ r0 = p ++ [.key fl] := by
          have h3 := hr
          rw [List.concat_eq_append, ← List.append_assoc,
            show p ++ [PE.key fl, PE.field n] = (p ++ [PE.key fl]) ++ [PE.field n] by simp] at h3
          exact (List.append_inj' h3 rfl).1
        exact hnc ⟨a, ha, ⟨r0, this⟩⟩
    · obtain ⟨-, -, t', hr, hat⟩ := (atomicNodes_mem_law_holds S t s _).1 ha
      exact (atomic_ne_granular S t _ t' hr hat hty).elim
  · intro n v r hn hr hm
    rcases (reconcile_mem_law_holds S t s _).1 hm with ⟨hs, -⟩ | ha
    · exact (h p fl).2.2 n v r hn hr hs
    · exact hkey p fl n v r hn ha

/-- A conforming value's field set has `keysWithItems`. -/
theorem kwi_fieldSet (S : Schema) (t : TypeRef) (x : UVal) (hwf : S.WF) (hc : conforms S t x) :
    keysWithItems S t (fieldSet S t x) := by
  sorry

/-! ## The trie nodes of a field set (at most the value's nodes) -/

mutual
/-- The paths of `x`'s nodes (at `p`, of type `t`) that a field set can reach: `p` and its
children's, along `fieldsAt`'s descent. -/
def nodesAt (S : Schema) (t : TypeRef) (p : Path) : UVal → PathSet
  | .list vs => PathSet.union (PathSet.single p) (match S.find t.name with
    | some (.list e _ ks) => nodesL S e ks p vs
    | _ => PathSet.empty)
  | .map kvs => PathSet.union (PathSet.single p) (match S.find t.name with
    | some (.map fs e _) => nodesM S fs e p kvs
    | _ => PathSet.empty)
  | .null => PathSet.single p
  | .bool _ => PathSet.single p
  | .int _ => PathSet.single p
  | .str _ => PathSet.single p
def nodesL (S : Schema) (e : TypeRef) (ks : List GoString) (p : Path) : List UVal → PathSet
  | [] => PathSet.empty
  | v :: vs => match keyOf ks v with
    | some pe => PathSet.union (nodesAt S e (p ++ [pe]) v) (nodesL S e ks p vs)
    | none => nodesL S e ks p vs
def nodesM (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (p : Path) :
    List (GoString × UVal) → PathSet
  | [] => PathSet.empty
  | (k, v) :: kvs => PathSet.union (match fieldType fs e k with
      | some t => nodesAt S t (p ++ [.field k]) v
      | none => PathSet.empty) (nodesM S fs e p kvs)
end

theorem card_single (p : Path) : (PathSet.single p).card ≤ 1 := LawA.card_ins p
theorem card_pempty : (PathSet.empty).card = 0 := rfl
theorem card_punion (a b : PathSet) : (PathSet.union a b).card ≤ a.card + b.card :=
  FSet_card_union_law_holds a b

mutual
theorem nodesAt_card (S : Schema) (t : TypeRef) (p : Path) :
    ∀ x : UVal, (nodesAt S t p x).card ≤ x.size
  | .list vs => by
    rw [nodesAt, UVal.size]
    have h1 := card_single p
    split
    · next e _ ks _ =>
      have := nodesL_card S p vs e ks
      have := card_punion (PathSet.single p) (nodesL S e ks p vs); omega
    · have := card_punion (PathSet.single p) PathSet.empty; rw [card_pempty] at this; omega
  | .map kvs => by
    rw [nodesAt, UVal.size]
    have h1 := card_single p
    split
    · next fs e _ _ =>
      have := nodesM_card S p kvs fs e
      have := card_punion (PathSet.single p) (nodesM S fs e p kvs); omega
    · have := card_punion (PathSet.single p) PathSet.empty; rw [card_pempty] at this; omega
  | .null => card_single p
  | .bool _ => card_single p
  | .int _ => card_single p
  | .str _ => card_single p
theorem nodesL_card (S : Schema) (p : Path) :
    ∀ vs : List UVal, ∀ (e : TypeRef) (ks : List GoString),
      (nodesL S e ks p vs).card ≤ UVal.sizeL vs
  | [] => fun e ks => by rw [nodesL, card_pempty]; omega
  | v :: vs => fun e ks => by
    have ih := nodesL_card S p vs e ks
    rw [nodesL, UVal.sizeL]
    split
    · next pe _ =>
      have h1 := nodesAt_card S e (p ++ [pe]) v
      have h2 := card_punion (nodesAt S e (p ++ [pe]) v) (nodesL S e ks p vs)
      omega
    · omega
theorem nodesM_card (S : Schema) (p : Path) :
    ∀ kvs : List (GoString × UVal), ∀ (fs : List (GoString × TypeRef)) (e : Option TypeRef),
      (nodesM S fs e p kvs).card ≤ UVal.sizeM kvs
  | [] => fun fs e => by rw [nodesM, card_pempty]; omega
  | (k, v) :: kvs => fun fs e => by
    have ih := nodesM_card S p kvs fs e
    rw [nodesM, UVal.sizeM]
    split
    · next t _ =>
      have h1 := nodesAt_card S t (p ++ [.field k]) v
      have h2 := card_punion (nodesAt S t (p ++ [.field k]) v) (nodesM S fs e p kvs); omega
    · have h2 := card_punion PathSet.empty (nodesM S fs e p kvs); rw [card_pempty] at h2; omega
end

theorem mem_single {p q : Path} : q ∈ PathSet.single p ↔ q = p ∧ q ≠ [] := by
  unfold PathSet.single
  rw [PathSet_mem_ofList_law_holds]; simp

theorem mem_punion {a b : PathSet} {q : Path} : q ∈ PathSet.union a b ↔ q ∈ a ∨ q ∈ b := by
  unfold PathSet.union; exact FSet_mem_union_law_holds a b q

theorem not_mem_pempty {q : Path} : q ∉ PathSet.empty := FSet.mem_empty q

theorem self_mem_nodesAt (S : Schema) (t : TypeRef) (p : Path) (hp : p ≠ []) (x : UVal) :
    p ∈ nodesAt S t p x := by
  cases x <;> simp only [nodesAt, mem_punion, mem_single] <;> simp [hp]

/-- Between `p` and `r`, below `p`'s child `p ++ [pe]` on the way to `r`: `p`, or below the child. -/
theorem prefix_step {p q r : Path} {pe : PE} (hpe : p ++ [pe] <+: r) (h1 : p <+: q)
    (h2 : q <+: r) : q = p ∨ p ++ [pe] <+: q := by
  by_cases hl : q.length ≤ p.length
  · exact Or.inl (h1.eq_of_length_le hl).symm
  · exact Or.inr (List.prefix_of_prefix_length_le hpe h2 (by simp; omega))

mutual
theorem nodesAt_sub (S : Schema) (t : TypeRef) (p : Path) :
    ∀ (x : UVal) (r : Path), r ∈ fieldsAt S t p x →
      p <+: r ∧ ∀ q, p <+: q → q <+: r → q ≠ [] → q ∈ nodesAt S t p x
  | .list vs, r, hr => by
    rw [fieldsAt] at hr
    split at hr
    · obtain ⟨rfl, -⟩ := mem_single.1 hr
      refine ⟨List.prefix_refl _, fun q h1 h2 hq => ?_⟩
      have := h2.eq_of_length_le h1.length_le; subst this
      exact self_mem_nodesAt S t _ hq _
    · next _ e rel ks _ hf =>
      obtain ⟨pe, hpe, hall⟩ := nodesL_sub S p vs e ks r hr
      refine ⟨(List.prefix_append p [pe]).trans hpe, fun q h1 h2 hq => ?_⟩
      rcases prefix_step hpe h1 h2 with rfl | hq'
      · exact self_mem_nodesAt S t _ hq _
      · simp only [nodesAt, hf]; exact mem_punion.2 (Or.inr (hall q hq' h2))
    · exact absurd hr not_mem_pempty
  | .map kvs, r, hr => by
    rw [fieldsAt] at hr
    split at hr
    · obtain ⟨rfl, -⟩ := mem_single.1 hr
      refine ⟨List.prefix_refl _, fun q h1 h2 hq => ?_⟩
      have := h2.eq_of_length_le h1.length_le; subst this
      exact self_mem_nodesAt S t _ hq _
    · next _ fs e rel _ hf =>
      obtain ⟨pe, hpe, hall⟩ := nodesM_sub S p kvs fs e r hr
      refine ⟨(List.prefix_append p [pe]).trans hpe, fun q h1 h2 hq => ?_⟩
      rcases prefix_step hpe h1 h2 with rfl | hq'
      · exact self_mem_nodesAt S t _ hq _
      · simp only [nodesAt, hf]; exact mem_punion.2 (Or.inr (hall q hq' h2))
    · exact absurd hr not_mem_pempty
  | .null, r, hr => by
    unfold fieldsAt at hr
    split at hr <;> first
      | exact absurd hr not_mem_pempty
      | (obtain ⟨rfl, -⟩ := mem_single.1 hr
         refine ⟨List.prefix_refl _, fun q h1 h2 hq => ?_⟩
         have := h2.eq_of_length_le h1.length_le; subst this
         exact self_mem_nodesAt S t _ hq _)
  | .bool _, r, hr => by
    unfold fieldsAt at hr
    split at hr <;> first
      | exact absurd hr not_mem_pempty
      | (obtain ⟨rfl, -⟩ := mem_single.1 hr
         refine ⟨List.prefix_refl _, fun q h1 h2 hq => ?_⟩
         have := h2.eq_of_length_le h1.length_le; subst this
         exact self_mem_nodesAt S t _ hq _)
  | .int _, r, hr => by
    unfold fieldsAt at hr
    split at hr <;> first
      | exact absurd hr not_mem_pempty
      | (obtain ⟨rfl, -⟩ := mem_single.1 hr
         refine ⟨List.prefix_refl _, fun q h1 h2 hq => ?_⟩
         have := h2.eq_of_length_le h1.length_le; subst this
         exact self_mem_nodesAt S t _ hq _)
  | .str _, r, hr => by
    unfold fieldsAt at hr
    split at hr <;> first
      | exact absurd hr not_mem_pempty
      | (obtain ⟨rfl, -⟩ := mem_single.1 hr
         refine ⟨List.prefix_refl _, fun q h1 h2 hq => ?_⟩
         have := h2.eq_of_length_le h1.length_le; subst this
         exact self_mem_nodesAt S t _ hq _)
theorem nodesL_sub (S : Schema) (p : Path) :
    ∀ (vs : List UVal) (e : TypeRef) (ks : List GoString) (r : Path), r ∈ fieldsL S e ks p vs →
      ∃ pe, p ++ [pe] <+: r ∧ ∀ q, p ++ [pe] <+: q → q <+: r → q ∈ nodesL S e ks p vs
  | [], e, ks, r, hr => by rw [fieldsL] at hr; exact absurd hr not_mem_pempty
  | v :: vs, e, ks, r, hr => by
    rw [fieldsL] at hr
    split at hr
    · next pe hk =>
      rcases mem_punion.1 hr with hr | hr
      · rcases mem_punion.1 hr with hr | hr
        · obtain ⟨hp, hall⟩ := nodesAt_sub S e (p ++ [pe]) v r hr
          refine ⟨pe, hp, fun q h1 h2 => ?_⟩
          simp only [nodesL, hk]
          exact mem_punion.2 (Or.inl (hall q h1 h2 (by rintro rfl; simp at h1)))
        · obtain ⟨rfl, hne⟩ := mem_single.1 hr
          refine ⟨pe, List.prefix_refl _, fun q h1 h2 => ?_⟩
          have := h2.eq_of_length_le h1.length_le; subst this
          simp only [nodesL, hk]; exact mem_punion.2 (Or.inl (self_mem_nodesAt S e _ hne v))
      · obtain ⟨pe', hp, hall⟩ := nodesL_sub S p vs e ks r hr
        refine ⟨pe', hp, fun q h1 h2 => ?_⟩
        simp only [nodesL, hk]; exact mem_punion.2 (Or.inr (hall q h1 h2))
    · next hk =>
      obtain ⟨pe', hp, hall⟩ := nodesL_sub S p vs e ks r hr
      exact ⟨pe', hp, fun q h1 h2 => by simp only [nodesL, hk]; exact hall q h1 h2⟩
theorem nodesM_sub (S : Schema) (p : Path) :
    ∀ (kvs : List (GoString × UVal)) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
      (r : Path), r ∈ fieldsM S fs e p kvs →
      ∃ pe, p ++ [pe] <+: r ∧ ∀ q, p ++ [pe] <+: q → q <+: r → q ∈ nodesM S fs e p kvs
  | [], fs, e, r, hr => by rw [fieldsM] at hr; exact absurd hr not_mem_pempty
  | (k, v) :: kvs, fs, e, r, hr => by
    rw [fieldsM] at hr
    rcases mem_punion.1 hr with hr | hr
    · split at hr
      · next t ht =>
        rcases mem_punion.1 hr with hr | hr
        · obtain ⟨hp, hall⟩ := nodesAt_sub S t (p ++ [.field k]) v r hr
          refine ⟨.field k, hp, fun q h1 h2 => ?_⟩
          simp only [nodesM, ht]
          exact mem_punion.2 (Or.inl (hall q h1 h2 (by rintro rfl; simp at h1)))
        · split at hr
          · obtain ⟨rfl, hne⟩ := mem_single.1 hr
            refine ⟨.field k, List.prefix_refl _, fun q h1 h2 => ?_⟩
            have := h2.eq_of_length_le h1.length_le; subst this
            simp only [nodesM, ht]; exact mem_punion.2 (Or.inl (self_mem_nodesAt S t _ hne v))
          · exact absurd hr not_mem_pempty
      · exact absurd hr not_mem_pempty
    · obtain ⟨pe', hp, hall⟩ := nodesM_sub S p kvs fs e r hr
      exact ⟨pe', hp, fun q h1 h2 => by simp only [nodesM]; exact mem_punion.2 (Or.inr (hall q h1 h2))⟩
end


/-- **A field set's trie nodes are at most the value's nodes** (`fieldSet_nodes`). -/
theorem fieldSet_nodes_le (S : Schema) (t : TypeRef) (x : UVal) :
    (fieldSet S t x).nodes.card ≤ x.size := by
  refine Nat.le_trans (FSet.card_le_of_subset _ (nodesAt S t [] x) ?_) (nodesAt_card S t [] x)
  intro q hq
  unfold PathSet.nodes at hq
  rw [FSet_mem_bind_law_holds] at hq
  obtain ⟨r, hr, hqr⟩ := hq
  unfold Path.nePrefixes at hqr
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hqr
  rw [List.mem_range] at hk
  refine (nodesAt_sub S t [] x r hr).2 _ (List.nil_prefix) (List.take_prefix _ _) ?_
  intro h
  have := congrArg List.length h
  rw [List.length_take, List.length_nil] at this; omega

theorem mem_mfUnion (mf : MF) (q : Path) : q ∈ mfUnion mf ↔ ∃ me ∈ mf, q ∈ me.2.set := by
  induction mf with
  | nil =>
    simp only [mfUnion, List.foldr_nil, List.not_mem_nil, false_and, exists_false, iff_false]
    exact not_mem_pempty
  | cons me rest ih =>
    have : mfUnion (me :: rest) = PathSet.union me.2.set (mfUnion rest) := rfl
    rw [this, mem_punion, ih]
    simp

theorem mem_nodes {s : PathSet} {q : Path} : q ∈ s.nodes ↔ ∃ r ∈ s, q ∈ Path.nePrefixes r := by
  unfold PathSet.nodes; exact FSet_mem_bind_law_holds _ _ _

/-- **`Apply`'s new managers' union** (the reconciled old entries, the applier's new one): its
trie nodes are at most the old union's and the new entry's. -/
theorem apply_union_nodes (S : Schema) (t : TypeRef) (mf : MF) (mgr : GoString) (e : VSet) :
    (mfUnion ((reconcileMF S t mf).set mgr e)).nodes.card ≤
      (mfUnion mf).nodes.card + e.set.nodes.card := by
  refine Nat.le_trans (FSet.card_le_of_subset _ (PathSet.union (mfUnion mf).nodes e.set.nodes) ?_)
    (card_punion _ _)
  intro q hq
  rw [mem_punion]
  obtain ⟨r, hr, hqr⟩ := mem_nodes.1 hq
  obtain ⟨me, hme, hrme⟩ := (mem_mfUnion _ r).1 hr
  rcases LawProofs.mem_insertKV hme with rfl | hme
  · exact Or.inr (mem_nodes.2 ⟨r, hrme, hqr⟩)
  · left
    unfold reconcileMF at hme
    obtain ⟨me0, hme0, rfl⟩ := List.mem_map.1 hme
    have hq0 := reconcile_nodes_sub S t me0.2.set q (mem_nodes.2 ⟨r, hrme, hqr⟩)
    obtain ⟨r', hr', hqr'⟩ := mem_nodes.1 hq0
    exact mem_nodes.2 ⟨r', (mem_mfUnion mf r').2 ⟨me0, hme0, hr'⟩, hqr'⟩

/-- **`prune`'s union bound from `inputsSmall`**: the applier's new managers' union (its new
entry the configuration's field set) stays below `smdSizeMax`. -/
theorem apply_union_small (S : Schema) (t : TypeRef) (live config : UVal) (mf : MF)
    (mgr : GoString) (ver : GoString) (h : inputsSmall [live, config] mf) :
    (mfUnion ((reconcileMF S t mf).set mgr ⟨fieldSet S t config, ver, true⟩)).nodes.card <
      smdSizeMax := by
  have h1 := apply_union_nodes S t mf mgr ⟨fieldSet S t config, ver, true⟩
  have h2 := fieldSet_nodes_le S t config
  simp only [inputsSmall, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
  simp only at h1
  omega

/-! ## Sizes -/

/-- Merging two conforming values adds no node beyond the two sides' (`merge_size`, with the
conformance premise `Apply` has). -/
theorem merge_size_conf (S : Schema) (t : TypeRef) (l r : UVal) (hwf : S.WF)
    (hl : conforms S t l) (hr : conforms S t r) : (merge S t l r).size ≤ l.size + r.size := by
  sorry

/-- Pruning adds no node (`prune_size`, from `removeItems_size`). -/
theorem prune_size_le (S : Schema) (t : TypeRef) (merged : UVal) (mf : MF) (last : Option VSet) :
    (prune S t merged mf last).size ≤ merged.size := by
  unfold prune
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact removeItems_size_law_holds S t merged _

/-! ## `Apply`'s premises of `prune` -/

/-- The applier's new managers (`mf0` with its entry `⟨fieldSet config, ver, true⟩`): every
entry at `ver`, with `keysWithItems`. -/
theorem apply_mf1_entries (S : Schema) (t : TypeRef) (config : UVal) (ver : GoString) (mf : MF)
    (mgr : GoString) (hwf : S.WF) (hc : conforms S t config)
    (hpre : ∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set) :
    ∀ m e, ((reconcileMF S t mf).set mgr ⟨fieldSet S t config, ver, true⟩).get m = some e →
      e.version = ver ∧ keysWithItems S t e.set := by
  intro m e h
  rw [MF.get_set_law_holds] at h
  split at h
  · cases h; exact ⟨rfl, kwi_fieldSet S t config hwf hc⟩
  · rw [reconcileMF_get_law_holds] at h
    obtain ⟨e0, he0, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hv, hk⟩ := hpre m e0 he0
    exact ⟨hv, kwi_reconcile S t e0.set hk⟩

/-- The applier's previous entry (reconciled): at `ver`, with `keysWithItems`, small. -/
theorem apply_last (S : Schema) (t : TypeRef) (ver : GoString) (mf : MF) (mgr : GoString)
    (_hwf : S.WF) (hpre : ∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set)
    (hsmall : (mfUnion mf).nodes.card < smdSizeMax) :
    ∀ L, (reconcileMF S t mf).get mgr = some L →
      L.version = ver ∧ keysWithItems S t L.set ∧ L.set.nodes.card < smdSizeMax := by
  intro L h
  rw [reconcileMF_get_law_holds] at h
  obtain ⟨e0, he0, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hv, hk⟩ := hpre mgr e0 he0
  refine ⟨hv, kwi_reconcile S t e0.set hk, ?_⟩
  have h1 := reconcile_nodes_le S t e0.set
  have h2 := mfUnion_nodes_law_holds mf mgr e0 he0
  simp only
  omega

end Glue

end smd
end EtcdGrove
end Perennial
