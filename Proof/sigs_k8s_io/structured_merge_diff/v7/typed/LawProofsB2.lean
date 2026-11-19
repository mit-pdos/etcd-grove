/-
**Proofs of the pure merge/compare laws of `typed`** (`WalkerLaws.lean`), part B2: `mergeO_some`,
`merge_conforms`, `cmpO_card`, with the facts they need of `mergeOrderF` (its keys come from its
inputs, each once; it is non-empty when an input is).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace LawB

/-! ## `mergeOrderF` -/

/-- What `mergeOrderF` may emit: a key still to come on the right, or a left-only key still to
come on the left. -/
def MOk (inR : PE → Bool) (L R : List PE) (x : PE) : Prop := x ∈ R ∨ (x ∈ L ∧ inR x = false)

theorem mergeOrderF_ok : ∀ (n : Nat) (inR : PE → Bool) (L R sh mg : List PE),
    L.Nodup → R.Nodup → (∀ x ∈ R, inR x = true) →
    (mergeOrderF n inR L R sh mg).Nodup ∧ ∀ x ∈ mergeOrderF n inR L R sh mg, MOk inR L R x
  | 0, _, _, _, _, _, _, _, _ => by simp [mergeOrderF]
  | n + 1, inR, L, R, sh, mg, hL, hR, hin => by
    -- the recursive calls, on sublists
    have hrec : ∀ L2 R2 sh2 mg2, L2.Sublist L → R2.Sublist R →
        (mergeOrderF n inR L2 R2 sh2 mg2).Nodup ∧
          ∀ x ∈ mergeOrderF n inR L2 R2 sh2 mg2, MOk inR L R x := by
      intro L2 R2 sh2 mg2 hL2 hR2
      obtain ⟨h1, h2⟩ := mergeOrderF_ok n inR L2 R2 sh2 mg2 (hL.sublist hL2) (hR.sublist hR2)
        (fun x hx => hin x (hR2.subset hx))
      refine ⟨h1, fun x hx => ?_⟩
      rcases h2 x hx with h | ⟨h, h'⟩
      · exact Or.inl (hR2.subset h)
      · exact Or.inr ⟨hL2.subset h, h'⟩
    -- an emitted head, then a recursive call on strict tails
    have cons : ∀ y L2 R2 sh2 mg2, MOk inR L R y → L2.Sublist L → R2.Sublist R →
        (∀ x ∈ mergeOrderF n inR L2 R2 sh2 mg2, x ≠ y) →
        (y :: mergeOrderF n inR L2 R2 sh2 mg2).Nodup ∧
          ∀ x ∈ y :: mergeOrderF n inR L2 R2 sh2 mg2, MOk inR L R x := by
      intro y L2 R2 sh2 mg2 hy hL2 hR2 hne
      obtain ⟨h1, h2⟩ := hrec L2 R2 sh2 mg2 hL2 hR2
      refine ⟨List.nodup_cons.2 ⟨fun hm => hne y hm rfl, h1⟩, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hy
      · exact h2 x hx
    -- a right key emitted: the rest comes from the right's tail or the left-only keys
    have consR : ∀ r R' L2 sh2 mg2, R = r :: R' → L2.Sublist L →
        (r :: mergeOrderF n inR L2 R' sh2 mg2).Nodup ∧
          ∀ x ∈ r :: mergeOrderF n inR L2 R' sh2 mg2, MOk inR L R x := by
      intro r R' L2 sh2 mg2 hRe hL2
      subst hRe
      refine cons r L2 R' sh2 mg2 (Or.inl (List.mem_cons_self ..)) hL2
        (List.sublist_cons_self _ _) ?_
      intro x hx hxr; subst hxr
      obtain ⟨_, h2⟩ := mergeOrderF_ok n inR L2 R' sh2 mg2 (hL.sublist hL2)
        (List.nodup_cons.1 hR).2 (fun x hx => hin x (List.mem_cons_of_mem _ hx))
      rcases h2 x hx with h | ⟨_, h'⟩
      · exact (List.nodup_cons.1 hR).1 h
      · rw [hin x (List.mem_cons_self ..)] at h'; exact Bool.noConfusion h'
    -- a left-only key emitted
    have consL : ∀ l L' R2 sh2 mg2, L = l :: L' → inR l = false → R2.Sublist R →
        (l :: mergeOrderF n inR L' R2 sh2 mg2).Nodup ∧
          ∀ x ∈ l :: mergeOrderF n inR L' R2 sh2 mg2, MOk inR L R x := by
      intro l L' R2 sh2 mg2 hLe hl hR2
      subst hLe
      refine cons l L' R2 sh2 mg2 (Or.inr ⟨List.mem_cons_self .., hl⟩)
        (List.sublist_cons_self _ _) hR2 ?_
      intro x hx hxl; subst hxl
      obtain ⟨_, h2⟩ := mergeOrderF_ok n inR L' R2 sh2 mg2 (List.nodup_cons.1 hL).2
        (hR.sublist hR2) (fun x hx => hin x (hR2.subset hx))
      rcases h2 x hx with h | ⟨h, _⟩
      · rw [hin x (hR2.subset h)] at hl; exact Bool.noConfusion hl
      · exact (List.nodup_cons.1 hL).1 h
    have hL2 : ∀ l L' (b : Prop) [Decidable b], L = l :: L' →
        (if b then L' else L).Sublist L := by
      intro l L' b _ hLe; split
      · subst hLe; exact List.sublist_cons_self _ _
      · exact List.Sublist.refl _
    rcases L with _ | ⟨l, L'⟩ <;> rcases R with _ | ⟨r, R'⟩
    · simp [mergeOrderF]
    · simp only [mergeOrderF]
      exact consR r R' [] _ _ rfl (List.nil_sublist _)
    · simp only [mergeOrderF]
      cases hi : inR l
      · simp only [Bool.not_false, ite_true]
        exact consL l L' [] sh mg rfl hi (List.Sublist.refl _)
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        exact hrec _ [] sh mg (hL2 l L' _ rfl) (List.Sublist.refl _)
    · by_cases hlr : l = r
      · subst hlr; simp only [mergeOrderF, ite_true]
        exact consR l R' L' _ _ rfl (List.sublist_cons_self _ _)
      · simp only [mergeOrderF, hlr, ite_false]
        rcases hsh : sh.head? with _ | s <;> cases hi : inR l <;>
          simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
            Bool.and_false, Bool.false_and, Bool.true_and, decide_eq_true_eq]
        all_goals first
          | exact consL l L' (r :: R') sh mg rfl hi (List.Sublist.refl _)
          | exact consR r R' _ _ _ rfl (hL2 l L' _ rfl)
          | skip
        by_cases hs : s = l
        · simp only [hs, ne_eq, not_true_eq_false, ite_false]
          exact consR r R' _ _ _ rfl (hL2 l L' _ rfl)
        · simp only [hs, ne_eq, not_false_eq_true, ite_true]
          exact hrec L' (r :: R') sh mg (List.sublist_cons_self _ _) (List.Sublist.refl _)

theorem mergeOrderF_ne : ∀ (n : Nat) (inR : PE → Bool) (L R sh mg : List PE),
    R ≠ [] → L.length < n → mergeOrderF n inR L R sh mg ≠ []
  | 0, _, _, _, _, _, _, h => by simp at h
  | n + 1, inR, L, R, sh, mg, hR, hn => by
    rcases R with _ | ⟨r, R'⟩
    · exact absurd rfl hR
    rcases L with _ | ⟨l, L'⟩
    · simp [mergeOrderF]
    · by_cases hlr : l = r
      · subst hlr; simp [mergeOrderF]
      · simp only [mergeOrderF, hlr, ite_false]
        rcases hsh : sh.head? with _ | s <;> cases hi : inR l <;>
          simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
            Bool.and_false, Bool.false_and, Bool.true_and, decide_eq_true_eq]
        all_goals first
          | exact List.cons_ne_nil _ _
          | skip
        by_cases hs : s = l
        · simp only [hs, ne_eq, not_true_eq_false, ite_false]; exact List.cons_ne_nil _ _
        · simp only [hs, ne_eq, not_false_eq_true, ite_true]
          exact mergeOrderF_ne n inR L' (r :: R') sh mg hR (by simp at hn; omega)

/-- **The merged keys**: each from an input, each once, some when an input has some. -/
theorem mergeKeys_mem (L R : List PE) (hL : L.Nodup) (hR : R.Nodup) (x : PE)
    (h : x ∈ mergeKeys L R) : x ∈ L ∨ x ∈ R := by
  rcases (mergeOrderF_ok _ _ L R _ _ hL hR (fun x hx => by simpa using hx)).2 x h with h | ⟨h, _⟩
  · exact Or.inr h
  · exact Or.inl h

theorem mergeKeys_nodup (L R : List PE) (hL : L.Nodup) (hR : R.Nodup) :
    (mergeKeys L R).Nodup :=
  (mergeOrderF_ok _ _ L R _ _ hL hR (fun x hx => by simpa using hx)).1

theorem mergeKeys_ne (L R : List PE) (h : L ≠ [] ∨ R ≠ []) : mergeKeys L R ≠ [] := by
  unfold mergeKeys
  by_cases hR : R = []
  · subst hR
    rcases L with _ | ⟨l, L'⟩
    · simp at h
    · simp [mergeOrderF]
  · exact mergeOrderF_ne _ _ _ _ _ _ hR (by omega)

/-! ## Keys, items, schema facts -/

theorem lkv_mem {α : Type} {k : GoString} : ∀ {xs : List (GoString × α)} {v : α},
    lookupKV k xs = some v → (k, v) ∈ xs
  | [], _, h => by simp [lookupKV] at h
  | (k', v') :: xs, v, h => by
    unfold lookupKV at h
    split at h
    · rename_i hk; cases h; subst hk; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lkv_mem h)

theorem find_wf (S : Schema) (hS : S.WF) (n : GoString) (a : Atom) (h : S.find n = some a) :
    a.wf S = true := by
  unfold Schema.WF at hS
  simp only [Bool.and_eq_true, List.all_eq_true] at hS
  exact hS.2 (n, a) (lkv_mem h)

/-- A granular list type of a schema in scope: associative, distinct keys, each a scalar field of
the element map type. -/
theorem list_wf (S : Schema) (hS : S.WF) (t e : TypeRef) (rel : ElemRel) (ks : List GoString)
    (h : S.find t.name = some (.list e rel ks)) (hr : rel ≠ .atomic) :
    rel = .associative ∧ ks.Nodup ∧ ∃ fs em rel', S.find e.name = some (.map fs em rel') ∧
      ∀ k ∈ ks, keyFieldOk S fs k = true := by
  have hw := find_wf S hS _ _ h
  simp only [Atom.wf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
  obtain ⟨_, h1 | ⟨⟨⟨h2, _⟩, h3⟩, h4⟩⟩ := hw
  · exact absurd h1 hr
  · refine ⟨h2, h3, ?_⟩
    split at h4
    · rename_i fs em rel' hf
      exact ⟨fs, em, rel', hf, fun k hk => (List.all_eq_true.1 h4) k hk⟩
    · exact absurd h4 (by simp)

theorem flInsert_perm (f : GoString × UVal) : ∀ l : FieldList, (flInsert f l).Perm (f :: l)
  | [] => List.Perm.refl _
  | g :: gs => by
    unfold flInsert
    split
    · exact List.Perm.refl _
    · exact ((flInsert_perm f gs).cons g).trans (List.Perm.swap f g gs)

theorem foldl_flInsert_perm : ∀ (fl acc : FieldList),
    (fl.foldl (fun acc f => flInsert f acc) acc).Perm (fl ++ acc)
  | [], acc => List.Perm.refl _
  | f :: fl, acc => by
    simp only [List.foldl_cons]
    exact (foldl_flInsert_perm fl _).trans
      ((List.Perm.append_left fl (flInsert_perm f acc)).trans List.perm_middle)

theorem flSort_perm (fl : FieldList) : (flSort fl).Perm fl := by
  have := foldl_flInsert_perm fl []
  rw [List.append_nil] at this
  exact this

theorem mem_keyFields (ks : List GoString) (kvs : List (GoString × UVal)) (k : GoString) (v : UVal) :
    (k, v) ∈ ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v))) ↔
      k ∈ ks ∧ lookupKV k kvs = some v := by
  simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', v', hv', rfl, rfl⟩; exact ⟨hk', hv'⟩
  · rintro ⟨hk, hv⟩; exact ⟨k, hk, v, hv, rfl, rfl⟩

theorem keyOf_map (ks : List GoString) (x : UVal) (pe : PE) (h : keyOf ks x = some pe) :
    ∃ kvs, x = .map kvs := by
  cases x <;> simp [keyOf] at h ⊢

/-- Two items of the same key agree on the key fields. -/
theorem keyOf_lookup_eq (ks : List GoString) (kvs1 kvs2 : List (GoString × UVal)) (pe : PE)
    (h1 : keyOf ks (.map kvs1) = some pe) (h2 : keyOf ks (.map kvs2) = some pe) :
    ∀ k ∈ ks, lookupKV k kvs1 = lookupKV k kvs2 := by
  simp only [keyOf] at h1 h2
  split at h1
  · cases h1
  split at h2
  · cases h2
  rw [← h2, Option.some.injEq, PE.key.injEq] at h1
  have hp := ((flSort_perm _).symm.trans (h1 ▸ flSort_perm _) :
    List.Perm (ks.filterMap (fun k => (lookupKV k kvs1).map (fun v => (k, v))))
      (ks.filterMap (fun k => (lookupKV k kvs2).map (fun v => (k, v)))))
  intro k hk
  apply Option.ext
  intro v
  have := hp.mem_iff (a := (k, v))
  rw [mem_keyFields, mem_keyFields] at this
  exact ⟨fun h => (this.1 ⟨hk, h⟩).2, fun h => (this.2 ⟨hk, h⟩).2⟩

theorem itemOf_some (ks : List GoString) (vs : List UVal) (pe : PE) (v : UVal)
    (h : itemOf ks vs pe = some v) : v ∈ vs ∧ keyOf ks v = some pe := by
  unfold itemOf at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem itemOf_of_keys (ks : List GoString) (vs : List UVal) (pe : PE) (h : pe ∈ keysOf ks vs) :
    (itemOf ks vs pe).isSome := by
  unfold itemOf
  unfold keysOf at h
  obtain ⟨v, hv, hk⟩ := List.mem_filterMap.1 h
  exact List.find?_isSome.2 ⟨v, hv, by simpa using hk⟩

theorem keysOf_ne (ks : List GoString) (vs : List UVal) (hne : vs ≠ [])
    (hk : ∀ v ∈ vs, (keyOf ks v).isSome) : keysOf ks vs ≠ [] := by
  obtain ⟨v, vs'⟩ := List.exists_cons_of_ne_nil hne
  rcases vs with _ | ⟨v, vs'⟩
  · exact absurd rfl hne
  · have := hk v (List.mem_cons_self ..)
    rcases h : keyOf ks v with _ | pe
    · simp [h] at this
    · simp [keysOf, h]

/-! ## `zipLexical` -/

theorem zipLexical_some : ∀ (f : Nat) (xs ys : List (GoString × UVal)) e,
    e ∈ zipLexical f xs ys → e.2.1.isSome ∨ e.2.2.isSome
  | 0, xs, ys, e, h => by simp [zipLexical] at h
  | f + 1, [], [], e, h => by simp [zipLexical] at h
  | f + 1, (k, a) :: xs, [], e, h => by
    simp only [zipLexical, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨k', a'⟩, _, rfl⟩ <;> simp
  | f + 1, [], (k, b) :: ys, e, h => by
    simp only [zipLexical, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨k', b'⟩, _, rfl⟩ <;> simp
  | f + 1, (k, a) :: xs, (k', b) :: ys, e, h => by
    simp only [zipLexical] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact zipLexical_some f xs ys e h
    · split at h
      · rcases List.mem_cons.1 h with rfl | h
        · simp
        · exact zipLexical_some f xs _ e h
      · rcases List.mem_cons.1 h with rfl | h
        · simp
        · exact zipLexical_some f _ ys e h

theorem zipLexical_ne : ∀ (f : Nat) (xs ys : List (GoString × UVal)),
    0 < f → (xs ≠ [] ∨ ys ≠ []) → zipLexical f xs ys ≠ []
  | 0, _, _, h, _ => by omega
  | f + 1, [], [], _, h => by simp at h
  | f + 1, (k, a) :: xs, [], _, _ => by simp [zipLexical]
  | f + 1, [], (k, b) :: ys, _, _ => by simp [zipLexical]
  | f + 1, (k, a) :: xs, (k', b) :: ys, _, _ => by
    simp only [zipLexical]
    split
    · simp
    · split <;> simp

theorem lkv_map_some {k : GoString} : ∀ (xs : List (GoString × UVal)),
    lookupKV k (xs.map (fun (k, a) => (k, (some a : Option UVal), (none : Option UVal)))) =
      (lookupKV k xs).map (fun a => (some a, none))
  | [] => rfl
  | (k', a) :: xs => by
    simp only [List.map_cons, lookupKV]
    split <;> simp [lkv_map_some xs]

theorem lkv_map_some' {k : GoString} : ∀ (ys : List (GoString × UVal)),
    lookupKV k (ys.map (fun (k, b) => (k, (none : Option UVal), (some b : Option UVal)))) =
      (lookupKV k ys).map (fun b => (none, some b))
  | [] => rfl
  | (k', b) :: ys => by
    simp only [List.map_cons, lookupKV]
    split <;> simp [lkv_map_some' ys]

theorem lkv_cons_ne {α : Type} {k k' : GoString} {v : α} {rest : List (GoString × α)}
    (h : k' ≠ k) : lookupKV k ((k', v) :: rest) = lookupKV k rest := by
  simp [lookupKV, h]

/-- What `zipLexical` pairs with a key: nothing iff neither side has it; else a side's first
entry or nothing (an unsorted side may have its first entry later). -/
def ZipLk (k : GoString) (xs ys : List (GoString × UVal)) (o : Option (Option UVal × Option UVal)) :
    Prop :=
  (o = none → lookupKV k xs = none ∧ lookupKV k ys = none) ∧
  ∀ a b, o = some (a, b) → (a = none ∨ a = lookupKV k xs) ∧ (b = none ∨ b = lookupKV k ys)

theorem zipLexical_lookup (k : GoString) : ∀ (f : Nat) (xs ys : List (GoString × UVal)),
    xs.length + ys.length < f → ZipLk k xs ys (lookupKV k (zipLexical f xs ys))
  | 0, _, _, h => by omega
  | f + 1, [], [], _ => by simp [ZipLk, zipLexical, lookupKV]
  | f + 1, (k0, a) :: xs, [], _ => by
    have e : zipLexical (f + 1) ((k0, a) :: xs) [] =
      ((k0, a) :: xs).map (fun (k, a) => (k, (some a : Option UVal), (none : Option UVal))) := rfl
    rw [e, lkv_map_some]
    refine ⟨fun h => ⟨by simpa using h, rfl⟩, fun a' b h => ?_⟩
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨v, hv, rfl, rfl⟩ := h
    exact ⟨Or.inr hv.symm, Or.inl rfl⟩
  | f + 1, [], (k0, b) :: ys, _ => by
    have e : zipLexical (f + 1) [] ((k0, b) :: ys) =
      ((k0, b) :: ys).map (fun (k, b) => (k, (none : Option UVal), (some b : Option UVal))) := rfl
    rw [e, lkv_map_some']
    refine ⟨fun h => ⟨rfl, by simpa using h⟩, fun a' b' h => ?_⟩
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨v, hv, rfl, rfl⟩ := h
    exact ⟨Or.inl rfl, Or.inr hv.symm⟩
  | f + 1, (k0, a) :: xs, (k1, b) :: ys, hf => by
    simp only [List.length_cons] at hf
    have cl : ∀ k0 a xs ys o, k0 ≠ k → ZipLk k xs ys o → ZipLk k ((k0, a) :: xs) ys o := by
      intro k0 a xs ys o hk h; unfold ZipLk at h ⊢; rw [lkv_cons_ne hk]; exact h
    have cr : ∀ k1 b xs ys o, k1 ≠ k → ZipLk k xs ys o → ZipLk k xs ((k1, b) :: ys) o := by
      intro k1 b xs ys o hk h; unfold ZipLk at h ⊢; rw [lkv_cons_ne hk]; exact h
    simp only [zipLexical]
    split
    · rename_i h01
      subst h01
      by_cases hk : k0 = k
      · subst hk; unfold ZipLk; simp [lookupKV]
      · simp only [lookupKV, hk, ite_false]
        exact cl _ _ _ _ _ hk (cr _ _ _ _ _ hk (zipLexical_lookup k f xs ys (by omega)))
    · split
      · by_cases hk : k0 = k
        · subst hk; unfold ZipLk; simp [lookupKV]
        · simp only [lookupKV, hk, ite_false]
          exact cl _ _ _ _ _ hk (zipLexical_lookup k f xs ((k1, b) :: ys) (by simp; omega))
      · by_cases hk : k1 = k
        · subst hk; unfold ZipLk; simp [lookupKV]
        · simp only [lookupKV, hk, ite_false]
          exact cr _ _ _ _ _ hk (zipLexical_lookup k f ((k0, a) :: xs) ys (by simp; omega))

theorem lkv_filterMap {β γ : Type} (g : GoString × β → Option (GoString × γ)) (k : GoString)
    (f : β → Option γ) (hk : ∀ e w, g e = some w → w.1 = e.1)
    (hf : ∀ e, e.1 = k → g e = (f e.2).map (fun v => (k, v))) :
    ∀ zs : List (GoString × β), (∀ e ∈ zs, e.1 = k → (f e.2).isSome) →
      lookupKV k (zs.filterMap g) = (lookupKV k zs).bind f
  | [], _ => rfl
  | e :: zs, hne => by
    have ih := lkv_filterMap g k f hk hf zs (fun e' h => hne e' (List.mem_cons_of_mem _ h))
    rw [List.filterMap_cons]
    obtain ⟨k', b⟩ := e
    by_cases he : k' = k
    · subst he
      have h1 := hne _ (List.mem_cons_self ..) rfl
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h1
      rw [hf _ rfl]
      simp only at hw ⊢
      simp [hw, lookupKV]
    · rw [lkv_cons_ne he]
      cases hg : g (k', b) with
      | none => exact ih
      | some w =>
        obtain ⟨k'', c⟩ := w
        have := hk _ _ hg; simp only at this; subst this
        simp only
        rw [lkv_cons_ne he]; exact ih

theorem zip_bind_leaf (k : GoString) (xs ys : List (GoString × UVal))
    (o : Option (Option UVal × Option UVal)) (hz : ZipLk k xs ys o)
    (hs : ∀ a b, o = some (a, b) → a.isSome ∨ b.isSome) (c : Option UVal)
    (hx : lookupKV k xs = c ∨ lookupKV k xs = none) (hy : lookupKV k ys = c ∨ lookupKV k ys = none)
    (hc : c = lookupKV k xs ∨ c = lookupKV k ys) :
    o.bind (fun ab => leafM ab.1 ab.2) = c := by
  rcases o with _ | ⟨a, b⟩
  · obtain ⟨h1, h2⟩ := hz.1 rfl
    rcases hc with rfl | rfl <;> simp [h1, h2]
  · obtain ⟨ha, hb⟩ := hz.2 a b rfl
    simp only [Option.bind_some, leafM]
    rcases b with _ | y
    · simp only
      have := hs _ _ rfl
      simp only [Option.isSome_none, Bool.false_eq_true, or_false] at this
      rcases ha with rfl | ha
      · simp at this
      · rw [ha]; rcases hx with h | h
        · exact h
        · rw [h] at ha; subst ha; simp at this
    · simp only
      rcases hb with h | hb
      · cases h
      · rw [hb]; rcases hy with h | h
        · exact h
        · rw [h] at hb; cases hb

/-- **Merging two items of a key keeps the key** (the key fields are scalars: the merged map has
each side's key fields). -/
theorem mergeF_keyOf (S : Schema) (e : TypeRef) (fs : List (GoString × TypeRef))
    (em : Option TypeRef) (rel' : ElemRel) (ks : List GoString)
    (hfind : S.find e.name = some (.map fs em rel')) (hkf : ∀ k ∈ ks, keyFieldOk S fs k = true)
    (pe : PE) (m : Nat) (a b : Option UVal) (hm : fuelO a b ≤ m)
    (ha : ∀ x, a = some x → keyOf ks x = some pe) (hb : ∀ y, b = some y → keyOf ks y = some pe)
    (v : UVal) (hv : mergeF m S e a b = some v) : keyOf ks v = some pe := by
  rcases m with _ | j
  · simp [mergeF] at hv
  simp only [mergeF, hfind] at hv
  by_cases hc : rel' = .atomic ∨ ((mapItems a).isEmpty ∧ (mapItems b).isEmpty)
  · rw [ite_eq_left hc] at hv
    rcases b with _ | y
    · exact ha v hv
    · simp only [leafM, Option.some.injEq] at hv; subst hv; exact hb y rfl
  rw [ite_eq_right hc] at hv
  generalize hout : List.filterMap _ (zipLexical _ (mapItems a) (mapItems b)) = out at hv
  split at hv
  · cases hv
  cases hv
  -- the reference side: one with the key
  have hab : a.isSome ∨ b.isSome := by
    rcases a with _ | x <;> rcases b with _ | y <;> simp_all [mapItems]
  -- the merged map has the reference side's key fields
  have hlk : ∀ k ∈ ks, ∀ kvs, (a = some (.map kvs) ∨ (a = none ∧ b = some (.map kvs))) →
      lookupKV k out = lookupKV k kvs := by
    intro k hk kvs hkvs
    subst hout
    have hkf' := hkf k hk
    unfold keyFieldOk at hkf'
    split at hkf'
    · rename_i kt hkt
      split at hkf'
      · rename_i sc hsc
        have hj : 1 ≤ j := by
          have : 1 ≤ sizeO a + sizeO b := by
            rcases hkvs with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> simp only [sizeO, UVal.size] <;> omega
          unfold fuelO at hm; omega
        have hft : fieldType fs em k = some kt := by simp [fieldType, hkt]
        rw [lkv_filterMap _ k (fun ab => leafM ab.1 ab.2)]
        · refine zip_bind_leaf k _ _ _ (zipLexical_lookup k _ _ _ (by omega))
            (fun a' b' h => zipLexical_some _ _ _ _ (lkv_mem h)) _ ?_ ?_ ?_
          all_goals rcases hkvs with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · rcases b with _ | y
            · exact Or.inr rfl
            · obtain ⟨kvs2, rfl⟩ := keyOf_map ks y pe (hb y rfl)
              exact Or.inl (keyOf_lookup_eq ks kvs2 kvs pe (hb _ rfl) (ha _ rfl) k hk)
          · exact Or.inl rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro ⟨k1, a1, b1⟩ w hw
          simp only at hw
          split at hw
          · simp only [Option.map_eq_some_iff] at hw
            obtain ⟨_, _, rfl⟩ := hw; rfl
          · cases hw
        · rintro ⟨k1, a1, b1⟩ h1
          simp only at h1; subst h1
          simp only [hft]
          rcases j with _ | j'
          · omega
          simp [mergeF, hsc]
        · rintro ⟨k1, a1, b1⟩ hmem _
          have := zipLexical_some _ _ _ _ hmem
          simp only at this ⊢
          rcases b1 with _ | y1 <;> simp_all [leafM]
      · simp at hkf'
    · simp at hkf'
  -- conclude: the same key fields as the reference side
  have href : ∃ kvs, (a = some (.map kvs) ∨ (a = none ∧ b = some (.map kvs))) ∧
      keyOf ks (.map kvs) = some pe := by
    rcases a with _ | x
    · rcases b with _ | y
      · simp at hab
      · obtain ⟨kvs, rfl⟩ := keyOf_map ks y pe (hb y rfl)
        exact ⟨kvs, Or.inr ⟨rfl, rfl⟩, hb _ rfl⟩
    · obtain ⟨kvs, rfl⟩ := keyOf_map ks x pe (ha x rfl)
      exact ⟨kvs, Or.inl rfl, ha _ rfl⟩
  obtain ⟨kvs, hkvs, hkey⟩ := href
  rw [← hkey]
  simp only [keyOf]
  rw [filterMap_congr_mem ks (fun k hk => congrArg (Option.map _) (hlk k hk kvs hkvs))]

/-! ## Conformance and presence of a merge -/

theorem confO_list (S : Schema) (t e : TypeRef) (ks : List GoString) (l : Option UVal)
    (hf : S.find t.name = some (.list e .associative ks)) (hl : confO S t l) :
    (∀ v ∈ listItems l, conforms S e v ∧ (keyOf ks v).isSome) ∧ (keysOf ks (listItems l)).Nodup := by
  rcases l with _ | ⟨_ | _ | _ | _ | vs | _⟩ <;> simp only [listItems, List.not_mem_nil,
    false_implies, implies_true, true_and, keysOf, List.filterMap_nil, List.nodup_nil]
  obtain ⟨h1, h2⟩ := LawA.conforms_item_law_holds S t e .associative ks vs hf hl
  obtain ⟨h3, h4⟩ := h2 rfl
  exact ⟨fun v hv => ⟨h1 v hv, h3 v hv⟩, h4⟩

theorem confO_map (S : Schema) (t : TypeRef) (fs : List (GoString × TypeRef)) (em : Option TypeRef)
    (rel : ElemRel) (l : Option UVal) (hf : S.find t.name = some (.map fs em rel))
    (hl : confO S t l) :
    ∀ k v, (k, v) ∈ mapItems l → ∃ t', fieldType fs em k = some t' ∧ conforms S t' v := by
  rcases l with _ | ⟨_ | _ | _ | _ | _ | kvs⟩ <;> simp only [mapItems, List.not_mem_nil,
    false_implies, implies_true]
  exact LawA.conforms_entry_law_holds S t fs em rel kvs hf hl

theorem confO_find (S : Schema) (t : TypeRef) (x : UVal) (h : confO S t (some x)) :
    (S.find t.name).isSome := by
  cases hf : S.find t.name with
  | some _ => rfl
  | none =>
    simp only [confO, conforms] at h
    cases x <;> simp [conformsB, hf] at h

theorem conformsM_of (S : Schema) (fs : List (GoString × TypeRef)) (em : Option TypeRef) :
    ∀ kvs : List (GoString × UVal),
      (∀ k v, (k, v) ∈ kvs → ∃ t', fieldType fs em k = some t' ∧ conforms S t' v) →
      conformsM S fs em kvs = true
  | [], _ => by simp [conformsM]
  | (k, v) :: kvs, h => by
    simp only [conformsM, Bool.and_eq_true]
    obtain ⟨t', ht, hc⟩ := h k v (List.mem_cons_self ..)
    refine ⟨by simp only [ht]; exact hc, conformsM_of S fs em kvs
      (fun k v hm => h k v (List.mem_cons_of_mem _ hm))⟩

theorem keysOf_filterMap (ks : List GoString) (f : PE → Option UVal) : ∀ (pes : List PE),
    (∀ pe ∈ pes, ∀ v, f pe = some v → keyOf ks v = some pe) →
    (keysOf ks (pes.filterMap f)).Sublist pes
  | [], _ => by simp [keysOf]
  | pe :: pes, h => by
    have ih := keysOf_filterMap ks f pes (fun p hp => h p (List.mem_cons_of_mem _ hp))
    rw [List.filterMap_cons]
    cases hf : f pe with
    | none => exact ih.cons pe
    | some v =>
      simp only [keysOf, List.filterMap_cons, h pe (List.mem_cons_self ..) v hf] at ih ⊢
      exact ih.cons_cons pe

theorem filterMap_ne {α β : Type} (f : α → Option β) (L : List α) (a : α) (ha : a ∈ L)
    (hs : (f a).isSome) : L.filterMap f ≠ [] := by
  intro h
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
  have : w ∈ L.filterMap f := List.mem_filterMap.2 ⟨a, ha, hw⟩
  rw [h] at this; simp at this

/-- **A merge of conforming sides conforms, and is present when a side is.** -/
theorem mergeF_conf (S : Schema) (hS : S.WF) : ∀ (n : Nat) (t : TypeRef) (l r : Option UVal),
    fuelO l r ≤ n → confO S t l → confO S t r →
    confO S t (mergeF n S t l r) ∧ ((l.isSome ∨ r.isSome) → (mergeF n S t l r).isSome)
  | 0, t, l, r, h, _, _ => by unfold fuelO at h; omega
  | n + 1, t, l, r, hn, hl, hr => by
    have hn' : sizeO l + sizeO r ≤ n := by unfold fuelO at hn; omega
    have leaf : confO S t (leafM l r) ∧ ((l.isSome ∨ r.isSome) → (leafM l r).isSome) := by
      rcases r with _ | y <;> rcases l with _ | x <;> simp_all [leafM, confO]
    simp only [mergeF]
    split
    · exact leaf
    · rename_i e rel ks hfind
      by_cases hc : rel = .atomic ∨ ((listItems l).isEmpty ∧ (listItems r).isEmpty)
      · rw [ite_eq_left hc]; exact leaf
      rw [ite_eq_right hc]
      have hrel : rel ≠ .atomic := fun h => hc (Or.inl h)
      obtain ⟨hassoc, _, fs, em, rel', hfe, hkf⟩ := list_wf S hS t e rel ks hfind hrel
      subst hassoc
      obtain ⟨hlc, hln⟩ := confO_list S t e ks l hfind hl
      obtain ⟨hrc, hrn⟩ := confO_list S t e ks r hfind hr
      have hne' : ¬((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true) :=
        fun h => hc (Or.inr h)
      have child : ∀ pe, pe ∈ mergeKeys (keysOf ks (listItems l)) (keysOf ks (listItems r)) →
          confO S e (mergeF n S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)) ∧
          (mergeF n S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)).isSome ∧
          ∀ v, mergeF n S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe) = some v →
            keyOf ks v = some pe := by
        intro pe hpe
        have hfu := (list_child_fuel ks l r pe hne').1
        have ca : confO S e (itemOf ks (listItems l) pe) := by
          cases h : itemOf ks (listItems l) pe with
          | none => trivial
          | some v => exact (hlc v (itemOf_some _ _ _ _ h).1).1
        have cb : confO S e (itemOf ks (listItems r) pe) := by
          cases h : itemOf ks (listItems r) pe with
          | none => trivial
          | some v => exact (hrc v (itemOf_some _ _ _ _ h).1).1
        have ih := mergeF_conf S hS n e _ _ (by omega) ca cb
        have hsome : (itemOf ks (listItems l) pe).isSome ∨ (itemOf ks (listItems r) pe).isSome := by
          rcases mergeKeys_mem _ _ hln hrn pe hpe with h | h
          · exact Or.inl (itemOf_of_keys _ _ _ h)
          · exact Or.inr (itemOf_of_keys _ _ _ h)
        exact ⟨ih.1, ih.2 hsome, fun v hv => mergeF_keyOf S e fs em rel' ks hfe hkf pe n _ _
          (by omega) (fun x hx => (itemOf_some _ _ _ _ hx).2)
          (fun y hy => (itemOf_some _ _ _ _ hy).2) v hv⟩
      have hpes_nd := mergeKeys_nodup _ _ hln hrn
      have hpes_ne : mergeKeys (keysOf ks (listItems l)) (keysOf ks (listItems r)) ≠ [] := by
        apply mergeKeys_ne
        by_cases hle : (listItems l).isEmpty = true
        · have hre : (listItems r).isEmpty = false := by
            cases h : (listItems r).isEmpty
            · rfl
            · exact absurd ⟨hle, h⟩ hne'
          exact Or.inr (keysOf_ne _ _ (by simpa using hre) (fun v hv => (hrc v hv).2))
        · exact Or.inl (keysOf_ne _ _ (by simpa using hle) (fun v hv => (hlc v hv).2))
      generalize mergeKeys (keysOf ks (listItems l)) (keysOf ks (listItems r)) = pes
        at child hpes_nd hpes_ne ⊢
      have hout_ne : pes.filterMap (fun pe =>
          mergeF n S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)) ≠ [] := by
        obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_ne_nil hpes_ne
        exact filterMap_ne _ _ p (List.mem_cons_self ..) (child p (List.mem_cons_self ..)).2.1
      have hsub := keysOf_filterMap ks _ pes (fun pe hpe v hv => (child pe hpe).2.2 v hv)
      generalize hout : pes.filterMap (fun pe =>
          mergeF n S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)) = out
        at hout_ne hsub ⊢
      have hmem : ∀ v ∈ out, conforms S e v ∧ (keyOf ks v).isSome := by
        intro v hv
        rw [← hout] at hv
        obtain ⟨pe, hpe, hv⟩ := List.mem_filterMap.1 hv
        have := child pe hpe
        refine ⟨?_, by rw [this.2.2 v hv]; rfl⟩
        have h1 := this.1; rw [hv] at h1; exact h1
      have hemp : out.isEmpty = false := by
        cases out
        · exact absurd rfl hout_ne
        · rfl
      simp only [hemp, Bool.false_eq_true, ite_false, Option.isSome_some, implies_true,
        and_true]
      simp only [confO, conforms, conformsB, hfind, ite_true, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨(LawA.conformsL_iff S e out).2 (fun v hv => (hmem v hv).1),
        fun v hv => (hmem v hv).2, hpes_nd.sublist hsub⟩
    · rename_i fs em rel hfind
      by_cases hc : rel = .atomic ∨ ((mapItems l).isEmpty ∧ (mapItems r).isEmpty)
      · rw [ite_eq_left hc]; exact leaf
      rw [ite_eq_right hc]
      have hlc := confO_map S t fs em rel l hfind hl
      have hrc := confO_map S t fs em rel r hfind hr
      have hne' : ¬((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true) :=
        fun h => hc (Or.inr h)
      have child : ∀ z ∈ zipLexical ((mapItems l).length + (mapItems r).length + 1)
          (mapItems l) (mapItems r), ∃ t', fieldType fs em z.1 = some t' ∧
            confO S t' (mergeF n S t' z.2.1 z.2.2) ∧ (mergeF n S t' z.2.1 z.2.2).isSome := by
        intro z hz
        have hfu := (map_child_fuel l r z hz hne').1
        obtain ⟨hz1, hz2⟩ := zipLexical_mem _ _ _ z hz
        have hs := zipLexical_some _ _ _ z hz
        have ht : ∃ t', fieldType fs em z.1 = some t' ∧ confO S t' z.2.1 ∧ confO S t' z.2.2 := by
          rcases ha : z.2.1 with _ | x
          · rcases hb : z.2.2 with _ | y
            · simp [ha, hb] at hs
            · obtain ⟨t', h1, h2⟩ := hrc _ _ (hz2 y hb)
              exact ⟨t', h1, trivial, h2⟩
          · obtain ⟨t', h1, h2⟩ := hlc _ _ (hz1 x ha)
            refine ⟨t', h1, h2, ?_⟩
            rcases hb : z.2.2 with _ | y
            · trivial
            · obtain ⟨t'', h1', h2'⟩ := hrc _ _ (hz2 y hb)
              rw [h1] at h1'; cases h1'; exact h2'
        obtain ⟨t', h1, ca, cb⟩ := ht
        have ih := mergeF_conf S hS n t' _ _ (by omega) ca cb
        exact ⟨t', h1, ih.1, ih.2 hs⟩
      have hzne : zipLexical ((mapItems l).length + (mapItems r).length + 1) (mapItems l)
          (mapItems r) ≠ [] := by
        apply zipLexical_ne _ _ _ (by omega)
        by_cases hle : (mapItems l).isEmpty = true
        · have hre : (mapItems r).isEmpty = false := by
            cases h : (mapItems r).isEmpty
            · rfl
            · exact absurd ⟨hle, h⟩ hne'
          exact Or.inr (by simpa using hre)
        · exact Or.inl (by simpa using hle)
      generalize zipLexical ((mapItems l).length + (mapItems r).length + 1) (mapItems l)
        (mapItems r) = zs at child hzne ⊢
      generalize hout : List.filterMap _ zs = out
      have hout_ne : out ≠ [] := by
        rw [← hout]
        obtain ⟨z, zs', rfl⟩ := List.exists_cons_of_ne_nil hzne
        obtain ⟨t', h1, _, h3⟩ := child z (List.mem_cons_self ..)
        apply filterMap_ne _ _ z (List.mem_cons_self ..)
        obtain ⟨k, a, b⟩ := z
        simp only at h1 h3 ⊢
        rw [h1]; simpa using h3
      have hmem : ∀ k v, (k, v) ∈ out → ∃ t', fieldType fs em k = some t' ∧ conforms S t' v := by
        intro k v hv
        rw [← hout] at hv
        obtain ⟨⟨k', a, b⟩, hz, hv⟩ := List.mem_filterMap.1 hv
        obtain ⟨t', h1, h2, _⟩ := child _ hz
        simp only at h1 h2 hv
        rw [h1] at hv
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hv
        obtain ⟨w, hw, rfl, rfl⟩ := hv
        rw [hw] at h2
        exact ⟨t', h1, h2⟩
      have hemp : out.isEmpty = false := by
        cases out
        · exact absurd rfl hout_ne
        · rfl
      simp only [hemp, Bool.false_eq_true, ite_false, Option.isSome_some, implies_true,
        and_true]
      simp only [confO, conforms, conformsB, hfind]
      exact conformsM_of S fs em out hmem
    · rename_i hfind
      refine ⟨trivial, fun h => ?_⟩
      exfalso
      rcases h with h | h
      · obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.1 h
        have := confO_find S t x hl; rw [hfind] at this; cases this
      · obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.1 h
        have := confO_find S t x hr; rw [hfind] at this; cases this

theorem mergeO_some_law_holds : mergeO_some.law := fun S t l r hS hl hr h =>
  (mergeF_conf S hS _ t l r (Nat.le_refl _) hl hr).2 h

theorem merge_conforms_law_holds : merge_conforms.law := by
  intro S t l r hS hl hr
  have h := (mergeF_conf S hS _ t (some l) (some r) (Nat.le_refl _) hl hr).1
  unfold merge
  unfold fuelO sizeO at h
  cases hm : mergeF (l.size + r.size + 1) S t (some l) (some r) with
  | some v => rw [hm] at h; exact h
  | none =>
    simp only [Option.getD_none]
    have hf := confO_find S t l hl
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hf
    simp only [conforms]
    unfold conformsB
    simp only [ha]
    cases a <;> simp [scalarOk]

/-! ## The size of a comparison -/

/-- The three sets' sizes together. -/
def cardAll (c : Cmp) : Nat := c.removed.card + c.modified.card + c.added.card

theorem cardAll_union (a b : Cmp) : cardAll (a.union b) ≤ cardAll a + cardAll b := by
  unfold cardAll Cmp.union
  have h1 := LawA.card_union a.removed b.removed
  have h2 := LawA.card_union a.modified b.modified
  have h3 := LawA.card_union a.added b.added
  simp only [union] at h1 h2 h3
  dsimp only
  omega

theorem cardAll_unionAll : ∀ cs : List Cmp, cardAll (Cmp.unionAll cs) ≤ (cs.map cardAll).sum
  | [] => by simp [Cmp.unionAll, Cmp.none, cardAll]; rfl
  | c :: cs => by
    have := cardAll_union c (Cmp.unionAll cs)
    have ih := cardAll_unionAll cs
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans this (by omega)

theorem cardAll_unionAll_le {α : Type} (F : α → Cmp) (g : α → Nat) : ∀ L : List α,
    (∀ x ∈ L, cardAll (F x) ≤ g x) → cardAll (Cmp.unionAll (L.map F)) ≤ (L.map g).sum
  | [], _ => by simp [Cmp.unionAll, Cmp.none, cardAll]; rfl
  | x :: L, h => by
    have := cardAll_union (F x) (Cmp.unionAll (L.map F))
    have ih := cardAll_unionAll_le F g L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans this (by omega)

theorem mem_unionAll (x : Path) : ∀ cs : List Cmp,
    (x ∈ (Cmp.unionAll cs).removed ↔ ∃ c ∈ cs, x ∈ c.removed) ∧
    (x ∈ (Cmp.unionAll cs).modified ↔ ∃ c ∈ cs, x ∈ c.modified) ∧
    (x ∈ (Cmp.unionAll cs).added ↔ ∃ c ∈ cs, x ∈ c.added)
  | [] => by
    simp only [Cmp.unionAll, List.foldr_nil, Cmp.none, List.not_mem_nil, false_and, exists_false,
      iff_false]
    exact ⟨FSet.mem_empty x, FSet.mem_empty x, FSet.mem_empty x⟩
  | c :: cs => by
    obtain ⟨h1, h2, h3⟩ := mem_unionAll x cs
    have e : Cmp.unionAll (c :: cs) = c.union (Cmp.unionAll cs) := rfl
    rw [e]
    simp only [Cmp.union, List.mem_cons, exists_eq_or_imp]
    refine ⟨?_, ?_, ?_⟩
    · rw [← h1]; exact FSet.mem_union' _ _ x
    · rw [← h2]; exact FSet.mem_union' _ _ x
    · rw [← h3]; exact FSet.mem_union' _ _ x

theorem cardAll_unionAll_dedup {α : Type} [DecidableEq α] (f : α → Cmp) (L : List α) :
    cardAll (Cmp.unionAll (L.map f)) ≤ cardAll (Cmp.unionAll ((FSet.dedupL L).map f)) := by
  have sub : ∀ c, c ∈ L.map f → c ∈ (FSet.dedupL L).map f := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    exact List.mem_map.2 ⟨a, (FSet.mem_dedupL L a).2 ha, rfl⟩
  unfold cardAll
  have h1 : (Cmp.unionAll (L.map f)).removed.card ≤
      (Cmp.unionAll ((FSet.dedupL L).map f)).removed.card :=
    FSet.card_le_of_subset _ _ (fun x hx => by
      obtain ⟨c, hc, hx⟩ := ((mem_unionAll x _).1).1 hx
      exact ((mem_unionAll x _).1).2 ⟨c, sub c hc, hx⟩)
  have h2 : (Cmp.unionAll (L.map f)).modified.card ≤
      (Cmp.unionAll ((FSet.dedupL L).map f)).modified.card :=
    FSet.card_le_of_subset _ _ (fun x hx => by
      obtain ⟨c, hc, hx⟩ := ((mem_unionAll x _).2.1).1 hx
      exact ((mem_unionAll x _).2.1).2 ⟨c, sub c hc, hx⟩)
  have h3 : (Cmp.unionAll (L.map f)).added.card ≤
      (Cmp.unionAll ((FSet.dedupL L).map f)).added.card :=
    FSet.card_le_of_subset _ _ (fun x hx => by
      obtain ⟨c, hc, hx⟩ := ((mem_unionAll x _).2.2).1 hx
      exact ((mem_unionAll x _).2.2).2 ⟨c, sub c hc, hx⟩)
  omega

theorem cardAll_leafC (p : Path) (l r : Option UVal) : cardAll (leafC p l r) ≤ 1 := by
  have := LawA.card_ins p
  unfold leafC cardAll
  rcases l with _ | a <;> rcases r with _ | b <;> simp only [LawA.card_empty] <;>
    try omega
  split <;> simp only [LawA.card_empty, Cmp.none] <;> omega

theorem sum_le_sum {α : Type} (f g : α → Nat) : ∀ L : List α, (∀ x ∈ L, f x ≤ g x) →
    (L.map f).sum ≤ (L.map g).sum
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_sum f g L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := h x (List.mem_cons_self ..)
    omega

theorem find_eraseP {α : Type} (p q : α → Bool) (h : ∀ x, p x = true → q x = false) :
    ∀ l : List α, (l.eraseP p).find? q = l.find? q
  | [] => rfl
  | x :: l => by
    rw [List.eraseP_cons]
    cases hp : p x
    · simp only [Bool.false_eq_true, ite_false, List.find?_cons]
      rw [find_eraseP p q h l]
    · simp only [ite_true, List.find?_cons, h x hp]

theorem size_eraseP (p : UVal → Bool) : ∀ l : List UVal,
    sizeO (l.find? p) + UVal.sizeL (l.eraseP p) = UVal.sizeL l
  | [] => rfl
  | x :: l => by
    rw [List.eraseP_cons, List.find?_cons]
    cases hp : p x
    · have := size_eraseP p l
      simp only [Bool.false_eq_true, ite_false, UVal.sizeL]
      omega
    · simp only [ite_true, UVal.sizeL, sizeO]

/-- Distinct keys pick distinct items. -/
theorem itemOf_sum (ks : List GoString) : ∀ (D : List PE) (vs : List UVal), D.Nodup →
    (D.map (fun pe => sizeO (itemOf ks vs pe))).sum ≤ UVal.sizeL vs
  | [], _, _ => by simp
  | pe :: D, vs, hD => by
    obtain ⟨hpe, hD'⟩ := List.nodup_cons.1 hD
    simp only [List.map_cons, List.sum_cons]
    have e : D.map (fun pe' => sizeO (itemOf ks vs pe')) =
        D.map (fun pe' => sizeO (itemOf ks (vs.eraseP (fun v => decide (keyOf ks v = some pe)))
          pe')) := by
      apply List.map_congr_left
      intro pe' hpe'
      unfold itemOf
      rw [find_eraseP]
      intro x hx
      simp only [decide_eq_true_eq] at hx
      simp only [hx, Option.some.injEq, decide_eq_false_iff_not]
      intro h; subst h; exact hpe hpe'
    rw [e]
    have ih := itemOf_sum ks D (vs.eraseP (fun v => decide (keyOf ks v = some pe))) hD'
    have := size_eraseP (fun v => decide (keyOf ks v = some pe)) vs
    unfold itemOf at ih ⊢
    omega

theorem zip_sum : ∀ (f : Nat) (xs ys : List (GoString × UVal)),
    ((zipLexical f xs ys).map (fun z => sizeO z.2.1 + sizeO z.2.2)).sum ≤
      UVal.sizeM xs + UVal.sizeM ys
  | 0, _, _ => by simp [zipLexical]
  | f + 1, [], [] => by simp [zipLexical]
  | f + 1, (k, a) :: xs, [] => by
    have : ∀ xs : List (GoString × UVal),
        ((xs.map (fun (k, a) => (k, (some a : Option UVal), (none : Option UVal)))).map
          (fun z => sizeO z.2.1 + sizeO z.2.2)).sum = UVal.sizeM xs := by
      intro xs; induction xs with
      | nil => rfl
      | cons kv xs ih =>
        obtain ⟨k, a⟩ := kv
        simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at ih ⊢
        omega
    have e : zipLexical (f + 1) ((k, a) :: xs) [] =
      ((k, a) :: xs).map (fun (k, a) => (k, (some a : Option UVal), (none : Option UVal))) := rfl
    rw [e, this ((k, a) :: xs)]
    exact Nat.le_add_right _ _
  | f + 1, [], (k, b) :: ys => by
    have : ∀ ys : List (GoString × UVal),
        ((ys.map (fun (k, b) => (k, (none : Option UVal), (some b : Option UVal)))).map
          (fun z => sizeO z.2.1 + sizeO z.2.2)).sum = UVal.sizeM ys := by
      intro ys; induction ys with
      | nil => rfl
      | cons kv ys ih =>
        obtain ⟨k, b⟩ := kv
        simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at ih ⊢
        omega
    have e : zipLexical (f + 1) [] ((k, b) :: ys) =
      ((k, b) :: ys).map (fun (k, b) => (k, (none : Option UVal), (some b : Option UVal))) := rfl
    rw [e, this ((k, b) :: ys)]
    exact Nat.le_add_left _ _
  | f + 1, (k, a) :: xs, (k', b) :: ys => by
    simp only [zipLexical]
    split
    · have := zip_sum f xs ys
      simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢
      omega
    · split
      · have := zip_sum f xs ((k', b) :: ys)
        simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢
        omega
      · have := zip_sum f ((k, a) :: xs) ys
        simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢
        omega

theorem cardAll_nodeC (p : Path) (l r : Option UVal) : cardAll (nodeC p l r) ≤ 1 ∧
    (l.isSome → r.isSome → cardAll (nodeC p l r) = 0) := by
  have := LawA.card_ins p
  unfold nodeC cardAll
  rcases l with _ | a <;> rcases r with _ | b <;>
    simp only [LawA.card_empty, Cmp.none, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, false_implies, true_implies, and_true] <;> omega

/-- **A comparison has at most as many paths as its sides have nodes** (one at least). -/
theorem cmpF_card (S : Schema) : ∀ (n : Nat) (t : TypeRef) (p : Path) (l r : Option UVal),
    fuelO l r ≤ n → cardAll (cmpF n S t p l r) ≤ max 1 (sizeO l + sizeO r)
  | 0, t, p, l, r, h => by unfold fuelO at h; omega
  | n + 1, t, p, l, r, hn => by
    have hn' : sizeO l + sizeO r ≤ n := by unfold fuelO at hn; omega
    have leaf := cardAll_leafC p l r
    simp only [cmpF]
    split
    · omega
    · rename_i e rel ks hfind
      by_cases hc : rel = .atomic ∨ ((listItems l).isEmpty ∧ (listItems r).isEmpty)
      · rw [ite_eq_left hc]; omega
      rw [ite_eq_right hc]
      have hne' : ¬((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true) :=
        fun h => hc (Or.inr h)
      generalize hpes : keysOf ks (listItems l) ++ (keysOf ks (listItems r)).filter
        (fun x => decide (x ∉ keysOf ks (listItems l))) = pes
      have hu := cardAll_union (Cmp.unionAll (pes.map (fun pe =>
        cmpF n S e (p ++ [pe]) (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe))))
        (nodeC p l r)
      have hd := cardAll_unionAll_dedup (fun pe =>
        cmpF n S e (p ++ [pe]) (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)) pes
      have hch := cardAll_unionAll_le (fun pe =>
        cmpF n S e (p ++ [pe]) (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe))
          (fun pe => sizeO (itemOf ks (listItems l) pe) +
          sizeO (itemOf ks (listItems r) pe)) (FSet.dedupL pes) (by
        intro pe hpe
        have hpe' := (FSet.mem_dedupL pes pe).1 hpe
        rw [← hpes] at hpe'
        have hsome : (itemOf ks (listItems l) pe).isSome ∨ (itemOf ks (listItems r) pe).isSome := by
          rcases List.mem_append.1 hpe' with h | h
          · exact Or.inl (itemOf_of_keys _ _ _ h)
          · exact Or.inr (itemOf_of_keys _ _ _ (List.mem_filter.1 h).1)
        have hfu := (list_child_fuel ks l r pe hne').1
        have ih := cmpF_card S n e (p ++ [pe]) (itemOf ks (listItems l) pe)
          (itemOf ks (listItems r) pe) (by omega)
        have : 1 ≤ sizeO (itemOf ks (listItems l) pe) + sizeO (itemOf ks (listItems r) pe) := by
          rcases hsome with h | h
          · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
            rw [hx]; have := size_pos x; simp only [sizeO]; omega
          · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
            rw [hx]; have := size_pos x; simp only [sizeO]; omega
        omega)
      have hsplit : ((FSet.dedupL pes).map (fun pe => sizeO (itemOf ks (listItems l) pe) +
          sizeO (itemOf ks (listItems r) pe))).sum =
          ((FSet.dedupL pes).map (fun pe => sizeO (itemOf ks (listItems l) pe))).sum +
          ((FSet.dedupL pes).map (fun pe => sizeO (itemOf ks (listItems r) pe))).sum := by
        induction FSet.dedupL pes with
        | nil => rfl
        | cons x xs ih => simp only [List.map_cons, List.sum_cons]; omega
      have hl := itemOf_sum ks (FSet.dedupL pes) (listItems l) (FSet.nodup_dedupL pes)
      have hr := itemOf_sum ks (FSet.dedupL pes) (listItems r) (FSet.nodup_dedupL pes)
      have hnode := cardAll_nodeC p l r
      -- the node: present on one side only, that side's items are counted with the node
      have hfin : UVal.sizeL (listItems l) + UVal.sizeL (listItems r) + cardAll (nodeC p l r) ≤
          sizeO l + sizeO r := by
        have b1 := listItems_size l
        have b2 := listItems_size r
        rcases l with _ | x <;> rcases r with _ | y
        · simp [listItems] at hne'
        · have := listItems_size_ne (some y) (by simpa [listItems] using hne')
          simp only [listItems, UVal.sizeL] at this ⊢; omega
        · have := listItems_size_ne (some x) (by simpa [listItems] using hne')
          simp only [listItems, UVal.sizeL] at this ⊢; omega
        · have := hnode.2 rfl rfl; omega
      omega
    · rename_i fs em rel hfind
      by_cases hc : rel = .atomic ∨ ((mapItems l).isEmpty ∧ (mapItems r).isEmpty)
      · rw [ite_eq_left hc]; omega
      rw [ite_eq_right hc]
      have hne' : ¬((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true) :=
        fun h => hc (Or.inr h)
      have hu := cardAll_union (Cmp.unionAll ((zipLexical ((mapItems l).length +
        (mapItems r).length + 1) (mapItems l) (mapItems r)).map (fun (k, a, b) =>
          match fieldType fs em k with
          | some t' => cmpF n S t' (p ++ [.field k]) a b
          | none => Cmp.none))) (nodeC p l r)
      have hch := cardAll_unionAll_le (fun (k, a, b) =>
          match fieldType fs em k with
          | some t' => cmpF n S t' (p ++ [.field k]) a b
          | none => Cmp.none) (fun z => sizeO z.2.1 + sizeO z.2.2) (zipLexical
          ((mapItems l).length + (mapItems r).length + 1) (mapItems l) (mapItems r)) (by
        rintro ⟨k, a, b⟩ hz
        have hfu := (map_child_fuel l r _ hz hne').1
        have hsome := zipLexical_some _ _ _ _ hz
        simp only at hfu hsome ⊢
        have : 1 ≤ sizeO a + sizeO b := by
          rcases hsome with h | h
          · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
            rw [hx]; have := size_pos x; simp only [sizeO]; omega
          · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
            rw [hx]; have := size_pos x; simp only [sizeO]; omega
        split
        · next t' _ =>
          have ih := cmpF_card S n t' (p ++ [.field k]) a b (by omega)
          omega
        · simp only [cardAll, Cmp.none, LawA.card_empty]; omega)
      have hz := zip_sum ((mapItems l).length + (mapItems r).length + 1) (mapItems l) (mapItems r)
      have hnode := cardAll_nodeC p l r
      have hfin : UVal.sizeM (mapItems l) + UVal.sizeM (mapItems r) + cardAll (nodeC p l r) ≤
          sizeO l + sizeO r := by
        have b1 := mapItems_size l
        have b2 := mapItems_size r
        rcases l with _ | x <;> rcases r with _ | y
        · simp [mapItems] at hne'
        · have := mapItems_size_ne (some y) (by simpa [mapItems] using hne')
          simp only [mapItems, UVal.sizeM] at this ⊢; omega
        · have := mapItems_size_ne (some x) (by simpa [mapItems] using hne')
          simp only [mapItems, UVal.sizeM] at this ⊢; omega
        · have := hnode.2 rfl rfl; omega
      refine Nat.le_trans hu ?_
      omega
    · simp only [cardAll, Cmp.none, LawA.card_empty]; omega

theorem cmpO_card_law_holds : cmpO_card.law := by
  intro S t p l r hl hr
  have h := cmpF_card S _ t p l r (Nat.le_refl _)
  unfold cmpO
  unfold cardAll at h
  simp only [smdSizeMax] at hl hr
  unfold FSet.CardLt
  refine ⟨?_, ?_, ?_⟩ <;> omega

end LawB

end smd
end EtcdGrove
end Perennial
