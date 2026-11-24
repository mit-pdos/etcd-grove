/-
The kv proof's lemmas: the abstract contents (`StoreS`) per key, and the items map of the lock
invariant (taking a key's entry out and putting it back).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace kvp

/-! ## The contents per key -/

theorem items_write_self (S : StoreS) (k x : GoString) (v : w64) :
    (S.write k x v).items k = S.items k ++ [(v, x, false)] := by
  simp [StoreS.write, StoreS.items, List.filter_append]

theorem items_write_ne (S : StoreS) (k k' x : GoString) (v : w64) (h : k' ≠ k) :
    (S.write k x v).items k' = S.items k' := by
  have : decide (k = k') = false := by simp [Ne.symm h]
  simp [StoreS.write, StoreS.items, List.filter_append, this]

/-- `Commit`'s first loop on one item: committed if its version is `v`. -/
def mark (v : w64) (e : Loc × It) : Loc × It :=
  if e.2.1 = v then (e.1, e.2.1, e.2.2.1, true) else e

/-- `Commit`'s second loop: the items kept (version at least `v`). -/
def keep (v : w64) (e : Loc × It) : Bool := decide (uint.Z v ≤ uint.Z e.2.1)

/-- `commit` on one key's items. -/
def commitIt (v : w64) (it : It) : Option It :=
  if uint.Z it.1 < uint.Z v then none else if it.1 = v then some (it.1, it.2.1, true) else some it

theorem items_commit_self (S : StoreS) (k : GoString) (v : w64) :
    (S.commit k v).items k = (S.items k).filterMap (commitIt v) := by
  induction S with
  | nil => rfl
  | cons e S ih =>
    obtain ⟨k', w, x, c⟩ := e
    by_cases hk : k' = k
    · subst hk
      by_cases h1 : uint.Z w < uint.Z v
      · simp_all [StoreS.commit, StoreS.items, commitIt]
      · by_cases h2 : w = v
        · subst h2; simp_all [StoreS.commit, StoreS.items, commitIt]
        · simp_all [StoreS.commit, StoreS.items, commitIt]
    · simp_all [StoreS.commit, StoreS.items]

theorem items_commit_ne (S : StoreS) (k k' : GoString) (v : w64) (h : k' ≠ k) :
    (S.commit k v).items k' = S.items k' := by
  induction S with
  | nil => rfl
  | cons e S ih =>
    obtain ⟨k'', w, x, c⟩ := e
    by_cases hk : k'' = k
    · subst hk
      by_cases h1 : uint.Z w < uint.Z v
      · simp_all [StoreS.commit, StoreS.items, Ne.symm h]
      · by_cases h2 : w = v
        · subst h2; simp_all [StoreS.commit, StoreS.items, Ne.symm h]
        · simp_all [StoreS.commit, StoreS.items, Ne.symm h]
    · by_cases hk' : k'' = k'
      · subst hk'; simp_all [StoreS.commit, StoreS.items]
      · simp_all [StoreS.commit, StoreS.items]

theorem commit_list (l : List (Loc × It)) (v : w64) :
    (l.map Prod.snd).filterMap (commitIt v) = (((l.map (mark v)).filter (keep v)).map Prod.snd) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨p, w, x, c⟩ := e
    by_cases h1 : uint.Z w < uint.Z v
    · have : ¬ w = v := by intro h; subst h; omega
      simp_all [commitIt, mark, keep]
    · by_cases h2 : w = v
      · subst h2; simp_all [commitIt, mark, keep]
      · simp_all [commitIt, mark, keep]

theorem hasVer_eq (S : StoreS) (k : GoString) (v : w64) (l : List (Loc × It))
    (h : S.items k = l.map Prod.snd) :
    S.hasVer k v = l.any (fun e => decide (e.2.1 = v)) := by
  simp [StoreS.hasVer, h, List.any_map, Function.comp_def]

theorem mark_id (l : List (Loc × It)) (v : w64) (h : l.any (fun e => decide (e.2.1 = v)) = false) :
    l.map (mark v) = l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [mark, h.1, ih h.2]

theorem commit_ne_nil (l : List (Loc × It)) (v : w64) (h : l.any (fun e => decide (e.2.1 = v)) = true) :
    (l.map (mark v)).filter (keep v) ≠ [] := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨p, w, x, c⟩ := e
    by_cases h2 : w = v
    · subst h2; simp [mark, keep]
    · have hl : l.any (fun e => decide (e.2.1 = v)) = true := by
        simpa [h2] using h
      have := ih hl
      simp only [List.map_cons, List.filter_cons]
      split
      · simp
      · exact this

theorem drop_cons_of_lookup {α : Type} (l : List α) (n : Nat) (e : α) (h : l[n]? = some e) :
    l.drop n = e :: l.drop (n + 1) := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hn

theorem take_succ_of_lookup {α : Type} (l : List α) (n : Nat) (e : α) (h : l[n]? = some e) :
    l.take (n + 1) = l.take n ++ [e] := by
  rw [List.take_succ, h]; rfl

theorem mark_fst (l : List (Loc × It)) (v : w64) : (l.map (mark v)).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    unfold mark; split <;> rfl

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [store.kv.Assumptions] [store.Assumptions]

/-- A big separating conjunction over a list gives one over a filter of it. -/
theorem sepL_filter {A : Type} (Φ : A → IProp GF) (l : List A) (p : A → Bool) :
    ([∗list] e ∈ l, Φ e) ⊢ [∗list] e ∈ l.filter p, Φ e := by
  induction l with
  | nil => exact .rfl
  | cons e l ih =>
    rw [List.filter_cons]
    split
    · iintro H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨He, H⟩
      iapply BigSepL.bigSepL_cons.2
      iframe He
      iapply ih $$ H
    · iintro H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨-, H⟩
      iapply ih $$ H

/-- Take key `k`'s entry out of the items map (an absent key has the nil slice, no items). -/
theorem map_take (m : GMap GoString GoSlice) (S : StoreS) (k : GoString)
    (Hnone : ∀ k, m !! k = none → S.items k = []) :
    ([∗map] k ↦ sl ∈ m, keyInv (hG := hG) S k sl) ⊢
      (∃ l : List (Loc × It), keyOwn k ((m !! k).getD slice.nil) l ∗
        ⌜S.items k = l.map Prod.snd ∧ ((m !! k).isSome → l ≠ []) ∧ ((m !! k) = none → l = [])⌝) ∗
      [∗map] k ↦ sl ∈ GMap.delete k m, keyInv (hG := hG) S k sl := by
  cases hk : m !! k with
  | none =>
    rw [GMap.delete_notin m k hk]
    iintro Hmap
    iframe Hmap
    iexists []
    unfold keyOwn
    simp only [List.map_nil, Option.getD_none, Option.isSome_none, Bool.false_eq_true,
      false_implies]
    isplitl []
    · isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      · iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
    · ipureintro; exact ⟨Hnone k hk, trivial, fun _ => trivial⟩
  | some sl =>
    iintro Hmap
    icases (BigSepM.bigSepM_delete (Φ := fun k sl => keyInv (hG := hG) S k sl) hk).1 $$ Hmap
      with ⟨Hk, Hrest⟩
    iframe Hrest
    unfold keyInv
    icases Hk with ⟨%l, Hk, %Hl⟩
    iexists l
    simp only [Option.getD_some, Option.isSome_some, forall_const]
    iframe Hk
    ipureintro; exact ⟨Hl.2, Hl.1, fun h => by cases h⟩

/-- Put key `k`'s entry back, unchanged. -/
theorem map_restore (m : GMap GoString GoSlice) (S : StoreS) (k : GoString) (l : List (Loc × It))
    (Hl : S.items k = l.map Prod.snd ∧ ((m !! k).isSome → l ≠ [])) :
    keyOwn (hG := hG) k ((m !! k).getD slice.nil) l ∗
      ([∗map] k ↦ sl ∈ GMap.delete k m, keyInv (hG := hG) S k sl) ⊢
      [∗map] k ↦ sl ∈ m, keyInv (hG := hG) S k sl := by
  cases hk : m !! k with
  | none =>
    rw [GMap.delete_notin m k hk]
    iintro ⟨-, H⟩
    iexact H
  | some sl =>
    iintro ⟨Hk, Hrest⟩
    iapply (BigSepM.bigSepM_delete (Φ := fun k sl => keyInv (hG := hG) S k sl) hk).2
    iframe Hrest
    unfold keyInv
    iexists l
    simp only [hk, Option.getD_some, Option.isSome_some, forall_const] at Hl ⊢
    iframe Hk
    ipureintro; exact ⟨Hl.2, Hl.1⟩

/-- The other keys' entries are unchanged by a change of `k`'s items. -/
theorem map_rest (m : GMap GoString GoSlice) (S S' : StoreS) (k : GoString)
    (h : ∀ k', k' ≠ k → S'.items k' = S.items k') :
    ([∗map] k ↦ sl ∈ GMap.delete k m, keyInv (hG := hG) S k sl) ⊢
      [∗map] k ↦ sl ∈ GMap.delete k m, keyInv (hG := hG) S' k sl := by
  apply BigSepM.bigSepM_mono
  intro k' sl' hk'
  have hne : k' ≠ k := by
    intro e; subst e
    have := GMap.lookup_delete m k'
    simp only [PartialMap.get?] at hk'
    rw [this] at hk'; cases hk'
  unfold keyInv
  iintro ⟨%l, Hk, %Hl⟩
  iexists l
  iframe Hk
  ipureintro
  exact ⟨Hl.1, by rw [h k' hne]; exact Hl.2⟩

/-- Put key `k`'s new entry back. -/
theorem map_put (m : GMap GoString GoSlice) (S : StoreS) (k : GoString) (sl : GoSlice) :
    keyInv (hG := hG) S k sl ∗ ([∗map] k ↦ sl ∈ GMap.delete k m, keyInv (hG := hG) S k sl) ⊢
      [∗map] k ↦ sl ∈ (<[k := sl]> m), keyInv (hG := hG) S k sl :=
  (BigSepM.bigSepM_insert_delete (Φ := fun k sl => keyInv (hG := hG) S k sl)).2

/-- The store's half and the client's share agree. -/
theorem own_agree (γs : GName) (q : Qp) (S S' : StoreS) :
    ghostVar (GF := GF) γs (1 : Qp).half S ⊢ storeOwn (hG := hG) γs q S' -∗ ⌜S' = S⌝ := by
  unfold storeOwn
  iintro H1 H2
  ihave %h := ghostVar_agree γs _ _ _ _ $$ H1 H2
  ipureintro; exact h.symm

/-- The store's half and the client's whole share: an update. -/
theorem own_update (γs : GName) (S S' S'' : StoreS) :
    ghostVar (GF := GF) γs (1 : Qp).half S ⊢ storeOwn (hG := hG) γs 1 S' ==∗
      ghostVar γs (1 : Qp).half S'' ∗ storeOwn (hG := hG) γs 1 S'' := by
  unfold storeOwn
  iintro H1 H2
  iapply ghostVar_update_halves S'' γs _ _ $$ H1 H2

/-- `store.ErrNotFound`'s value, from the package's initialization. -/
theorem errNotFound_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store.kv ⊢
      ∃ err, errNotFound (hG := hG) err := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) _).trans ?_
  show iprop(isPkgInit pkg_id.log ∗ isPkgInit pkg_id.sync ∗
    isPkgInit pkg_id.github_com.despreston.go_craq.store ∗ True) ⊢ _
  iintro ⟨-, -, #H, -⟩
  ihave #Hs := isPkgInit_access $$ H
  ihave #Hs' : (errors.newVar store.ErrNotFound go!"that key does not exist" ∗
    errors.newVar store.ErrDirtyItem go!"key has an uncommitted version" : IProp GF) $$ [Hs]
  · iexact Hs
  icases Hs' with ⟨#He, -⟩
  unfold errors.newVar
  icases He with ⟨%x, #Hx, #Hs, #Hmsg⟩
  iexists interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x
  unfold errNotFound
  iexists x
  isplitr
  · ipureintro; rfl
  iframe Hx Hs Hmsg

/-- `s.lookup(key)`: the key's slice and whether it is present (a present key's slice is not
empty). -/
theorem wp_lookup (p mp : Loc) (m : GMap GoString GoSlice) (k : GoString) (ps : List Loc)
    (Hne : (m !! k).isSome → ps ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store.kv ∗
        structFieldRef store.kv.KV go!"items" p ↦□ mp ∗ mp ↦$ m ∗
        (m !! k).getD slice.nil ↦* ps }}
      (App (Val (p @!! go.GoType.PointerType store.kv.KV.ty @!! go!"lookup")) (Val #k))
    {{ RET (PairV #((m !! k).getD slice.nil) #((m !! k).isSome));
        mp ↦$ m ∗ (m !! k).getD slice.nil ↦* ps }} := by
  wp_start as ⟨#Hitems, Hm, Hsl⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ Hm as Hm
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  cases hk : m !! k with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    wp_if_destruct
    · iapply HΦ
      iframe
    · exact absurd rfl Hif
  | some sl =>
    simp only [hk, Option.getD_some, Option.isSome_some, forall_const] at Hne Hlen ⊢
    have : sl.len ≠ W64 0 := by
      intro h; rw [h] at Hlen
      apply Hne; apply List.eq_nil_of_length_eq_zero
      have := Hlen.1; rw [this]; rfl
    wp_if_destruct
    · exact absurd Hif this
    · iapply HΦ
      iframe

end lemmas

end kvp

end github_com.despreston.go_craq

end Perennial
