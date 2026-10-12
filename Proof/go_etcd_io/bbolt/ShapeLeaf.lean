/-
A leaf's entries changed by `Bucket.Put`/`Bucket.Delete` (`node.put`, `node.del` on the leaf a
cursor found for the key): the write transaction keeps its shape (`txShape`).

The leaf's entries `A ++ D ++ C` become `A ++ E ++ C`: `D` (the entry with the key, if any) is
not a nested bucket's (`Put`/`Delete` fail on one: the cursor's flags, `pathKey`), `E` (the entry
put, if any) is not one either and has a key within the leaf's bounds (the key the cursor routed
there, `kroute`). Then
- the keys stay a B+tree's (`bktKeysB_leafOp`, same bounds): the leaf is no node's parent;
- the nested buckets' entries stay (`entryIn_leafOp`): only `D` is removed;
- the tokens stay (`nodeToks_leafOp`): a leaf's tokens are its unopened nested buckets' trees,
  which are in `A` and `C` (those of `D`, none, would be dropped);
- the transaction's shape (`txShape_open`, `txShape_close`): the bucket's tokens are split out
  of `txShape`, and put back with the bucket's new record; the other buckets' `bktNested` sees
  the same root (`ib`) and a materialized root node.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.PathFlags

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- A list with an element put at `i` (`putList`), as a middle part replaced. -/
theorem putList_split {α : Type} (l : List α) (i : Nat) (ex : Bool) (x : α)
    (hi : ex = true → i < l.length) :
    ∃ A D C, l = A ++ D ++ C ∧ putList l i ex x = A ++ [x] ++ C ∧
      ∀ w ∈ D, ex = true ∧ l[i]? = some w := by
  unfold putList
  cases ex with
  | true =>
    have h := hi rfl
    refine ⟨l.take i, [l[i]], l.drop (i + 1), ?_, ?_, ?_⟩
    · simp
    · rw [List.set_eq_take_append_cons_drop]; simp [h]
    · intro w hw; simp at hw; subst hw; exact ⟨rfl, List.getElem?_eq_getElem h⟩
  | false =>
    refine ⟨l.take i, [], l.drop i, by simp, by simp, by simp⟩

/-- A list with element `i` erased, as a middle part removed. -/
theorem eraseIdx_split {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    ∃ A D C, l = A ++ D ++ C ∧ l.eraseIdx i = A ++ [] ++ C ∧ ∀ w ∈ D, l[i]? = some w := by
  refine ⟨l.take i, [l[i]], l.drop (i + 1), ?_, ?_, ?_⟩
  · simp
  · rw [List.eraseIdx_eq_take_drop_succ]; simp
  · intro w hw; simp at hw; subst hw; exact List.getElem?_eq_getElem hi

theorem ns_insert_lookup (B : BRec) (l : Loc) (r' : NRec) (y : Loc) :
    (<[l := r']> B.ns) !! y = if y = l then some r' else B.ns !! y := by
  by_cases h : y = l
  · subst h; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]

/-- The leaf `l` is no node's parent (a parent is a branch). -/
theorem leaf_not_parent (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (l : Loc) (r : NRec) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hp : ry.nv.parent' ≠ null) :
    ry.nv.parent' ≠ l := by
  intro h
  obtain ⟨rp, hrp, hl, -⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
  rw [h, hr] at hrp; cases hrp; rw [hleaf] at hl; cases hl

/-- The leaf's record changed as by `Put`/`Delete`: the keys stay a B+tree's. -/
theorem bktKeysB_leafOp (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB W B bnd)
    (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, keyIn (bnd l).1 (bnd l).2 w.key ∧ ¬ isBktFlag w.flags)
    (e1 : r'.nv.isLeaf' = true) (e2 : r'.nv.parent' = r.nv.parent') (e3 : r'.nv.pgid' = r.nv.pgid')
    (e4 : r'.nv.key' = r.nv.key') (e5 : r'.key = r.key)
    (hne : r'.nv.unbalanced' = false → 0 < r'.ws.length) :
    bktKeysB W { B with ns := <[l := r']> B.ns } bnd := by
  obtain ⟨hk1, hkr, hk2⟩ := hk
  have hmem : ∀ w ∈ r'.ws, w ∈ r.ws ∨ w ∈ E := by
    intro w hw
    rw [hws'] at hw; rw [hws]
    simp only [List.mem_append] at hw ⊢
    rcases hw with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hnl := leaf_not_parent W hwm bl B hc l r hr hleaf
  refine ⟨hk1, ?_, ?_⟩
  · intro r0 h0
    show r0.nv.parent' = null
    simp only at h0
    rw [ns_insert_lookup] at h0
    by_cases h : B.bv.rootNode' = l
    · rw [if_pos h] at h0; cases h0; rw [e2]; exact hkr r (by rw [h]; exact hr)
    · rw [if_neg h] at h0; exact hkr r0 h0
  intro y ry hy
  simp only at hy
  rw [ns_insert_lookup] at hy
  by_cases hyl : y = l
  · rw [if_pos hyl] at hy; cases hy; subst hyl
    obtain ⟨c1, c2, c3, -, -, c6⟩ := hk2 y r hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases hmem w hw with h | h
      · exact c1 w h
      · exact (hE w h).1
    · rw [e2]; exact c2
    · intro hp
      rw [e2] at hp
      obtain ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, hb⟩ := c3 hp
      have hpl : r.nv.parent' ≠ y := hnl y r hr hp
      refine ⟨by rw [e4]; exact hkey, rp, i, w, ?_, hw, by rw [hpg, e3], by rw [hwk, e5], by rw [e2]; exact hb⟩
      show (<[y := r']> B.ns) !! r'.nv.parent' = _
      rw [e2, ns_insert_lookup, if_neg hpl]; exact hrp
    · intro h; rw [e1] at h; cases h
    · intro _ hu _; exact hne hu
    · intro _ w hw hb
      rcases hmem w hw with h | h
      · exact c6 hleaf w h hb
      · exact absurd hb (hE w h).2
  · rw [if_neg hyl] at hy
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hk2 y ry hy
    refine ⟨c1, c2, ?_, ?_, c5, c6⟩
    · intro hp
      obtain ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, hb⟩ := c3 hp
      have hpl : ry.nv.parent' ≠ l := hnl y ry hy hp
      refine ⟨hkey, rp, i, w, ?_, hw, hpg, hwk, hb⟩
      show (<[l := r']> B.ns) !! ry.nv.parent' = _
      rw [ns_insert_lookup, if_neg hpl]; exact hrp
    · intro hb
      obtain ⟨h2, kind, hkind⟩ := c4 hb
      refine ⟨h2, kind, fun i w hw => ⟨?_, (hkind i w hw).2⟩⟩
      intro l' hl'
      obtain ⟨r0, h0, hk0⟩ := (hkind i w hw).1 l' hl'
      show ∃ r'', (<[l := r']> B.ns) !! l' = some r'' ∧ _
      rw [ns_insert_lookup]
      by_cases h : l' = l
      · subst h; rw [hr] at h0; cases h0
        exact ⟨r', by rw [if_pos rfl], by rw [e1, ← hk0, hleaf]⟩
      · exact ⟨r0, by rw [if_neg h]; exact h0, hk0⟩

/-- The leaf's record changed as by `Put`/`Delete`: its page positions are the same. -/
theorem posRoot_leafOp (B : BRec) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (c : Nat) :
    posRoot { B with ns := <[l := r']> B.ns } c ↔ posRoot B c := by
  have hpos : ∀ x i c, pagePosAt { B with ns := <[l := r']> B.ns } x i c ↔ pagePosAt B x i c := by
    intro x i c
    unfold pagePosAt
    constructor
    · rintro ⟨ry, w, hy, hl, hw, hp, hn⟩
      simp only at hy
      rw [ns_insert_lookup] at hy
      by_cases h : x = l
      · rw [if_pos h] at hy; cases hy; rw [e1] at hl; cases hl
      · rw [if_neg h] at hy; exact ⟨ry, w, hy, hl, hw, hp, hn⟩
    · rintro ⟨ry, w, hy, hl, hw, hp, hn⟩
      have hx : x ≠ l := by
        intro h; subst h; rw [hr] at hy; cases hy; rw [hleaf] at hl; cases hl
      exact ⟨ry, w, by show (<[l := r']> B.ns) !! x = _; rw [ns_insert_lookup, if_neg hx]; exact hy,
        hl, hw, hp, hn⟩
  unfold posRoot
  simp only [hpos]

/-- The leaf's record changed as by `Put`/`Delete`, the entries removed not nested buckets':
the nested buckets' entries stay. -/
theorem entryIn_leafOp (W : WView) (B : BRec) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true)
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hD : ∀ w ∈ D, ¬ isBktFlag w.flags) (k v : List w8) (h : entryIn W B k v) :
    entryIn W { B with ns := <[l := r']> B.ns } k v := by
  rcases h with ⟨y, ry, w, hy, hl, hw, hk, hb, hv⟩ | ⟨c, p, pg, i, hc, hrest⟩
  · left
    by_cases hyl : y = l
    · subst hyl; rw [hr] at hy; cases hy
      have hw' : w ∈ r'.ws := by
        rw [hws] at hw; rw [hws']
        simp only [List.mem_append] at hw ⊢
        rcases hw with (h | h) | h
        · exact Or.inl (Or.inl h)
        · exact absurd hb (hD w h)
        · exact Or.inr h
      exact ⟨y, r', w, by show (<[y := r']> B.ns) !! y = _; rw [GMap.lookup_insert], e1, hw', hk, hb, hv⟩
    · exact ⟨y, ry, w, by show (<[l := r']> B.ns) !! y = _; rw [ns_insert_lookup, if_neg hyl]; exact hy,
        hl, hw, hk, hb, hv⟩
  · right
    exact ⟨c, p, pg, i, (posRoot_leafOp B l r r' hr hleaf e1 c).2 hc, hrest⟩

/-- The entry `i` of a leaf has the key the cursor searched for: it is the one returned
(`pathKey`). -/
theorem pathKey_at (ws : List WEntry) (i : Nat) (w : WEntry) (kb kbs : List w8) (f : w32)
    (hw : ws[i]? = some w) (hk : wKey ws i = kb)
    (hP : ∀ w ∈ ws, w.key = kb → w.flags = f ∧ kbs = kb) : w.flags = f ∧ kbs = kb :=
  hP w (List.mem_of_getElem? hw) (by simpa [wKey, hw] using hk)

end pure

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- A list's middle part `D` replaced by `E`, whose elements need nothing. -/
theorem bigSepL_mid {A : Type} (Φ : A → IProp GF) (X D C E : List A) (hE : ∀ w ∈ E, emp ⊢ Φ w) :
    ([∗list] w ∈ X ++ D ++ C, Φ w) ⊢ [∗list] w ∈ X ++ E ++ C, Φ w := by
  have hE' : (emp : IProp GF) ⊢ [∗list] w ∈ E, Φ w :=
    (BigSepL.bigSepL_emp (PROP := IProp GF) (l := E)).2.trans
      (BigSepL.bigSepL_mono (fun {k x} h => hE x (List.mem_of_getElem? h)))
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H3⟩
  icases BigSepL.bigSepL_append.1 $$ H1 with ⟨H1, -⟩
  iapply BigSepL.bigSepL_append.2
  isplitl [H1]
  · iapply BigSepL.bigSepL_append.2
    isplitl [H1]
    · iexact H1
    · iapply hE'
      iempintro
  · iexact H3

/-- The leaf's record changed as by `Put`/`Delete`: its tokens stay. -/
theorem nodeToks_leafOp (γ : GName) (W : WView) (B : BRec) (r r' : NRec)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (e3 : r'.nv.pgid' = r.nv.pgid')
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, ¬ isBktFlag w.flags) :
    nodeToks γ W B r ⊢ nodeToks γ W B r' := by
  unfold nodeToks
  rw [e3, e1, hleaf, hws, hws']
  iintro ⟨Hp, Hl⟩
  iframe Hp
  iapply bigSepL_mid _ A D C E ?_ $$ Hl
  intro w hw
  have hb := hE w hw
  simp only [↓reduceIte, hb, false_and]
  exact .rfl

/-- The leaf's record changed as by `Put`/`Delete`: the bucket's tokens stay. -/
theorem bktToks_leafOp (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (e3 : r'.nv.pgid' = r.nv.pgid')
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, ¬ isBktFlag w.flags) :
    bktToks γ W B ⊢ bktToks γ W { B with ns := <[l := r']> B.ns } := by
  have hrn : B.bv.rootNode' ≠ null := by
    intro h; rw [(hc.2.2.1 h).1] at hr; cases hr
  have hns : ∀ r0, nodeToks γ W { B with ns := <[l := r']> B.ns } r0 = nodeToks γ W B r0 :=
    fun _ => rfl
  unfold bktToks
  simp only [if_neg hrn, hns]
  iintro H
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
    (show Std.get? B.ns l = some r from hr)) $$ H with ⟨Hn, Hback⟩
  ihave Hn := nodeToks_leafOp γ W B r r' hleaf e1 e3 A D C E hws hws' hE $$ Hn
  iapply Hback $$ %r' Hn

end toks

section tx
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The transaction's shape without the tokens of its bucket `bl` (`txShape_open`). -/
def txFrame (γ : GName) (W : WView) (T : WTx) (bl : Loc) : IProp GF :=
  iprop(∃ (M : GMap Nat Unit), ghostMapAuth γ 1 M ∗
    ⌜∀ id, (M !! id).isSome ↔ (W.pages !! id).isSome⌝ ∗
    (∀ B', bktToks γ W B' -∗ [∗map] _bl ↦ B ∈ <[bl := B']> T.bs, bktToks γ W B) ∗
    ⌜∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktNested W T B⌝)

/-- The shape of the bucket `bl` split out of the transaction's. -/
theorem txShape_open (γ : GName) (W : WView) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    txShape (GF := GF) γ W T ⊢ bktShape γ W B ∗ txFrame γ W T bl ∗
      ⌜∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktNested W T B⌝ := by
  unfold txShape
  iintro ⟨%M, Ha, %Hd, Hbs, %Hf⟩
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun _ B => bktToks (GF := GF) γ W B)
    (show Std.get? T.bs bl = some B from hB)) $$ Hbs with ⟨Hb, Hback⟩
  isplitl [Hb]
  · unfold bktShape; iframe Hb; ipureintro; exact (Hf bl B hB).1
  isplitl
  · unfold txFrame; iexists M; iframe Ha; isplitr
    · ipureintro; exact Hd
    isplitl
    · iintro %B' Hb'; iapply Hback $$ %B' Hb'
    · ipureintro; exact Hf
  · ipureintro; exact Hf

/-- The facts of the transaction with the bucket `bl`'s record `B''` (its root, its header if
it has no root node, its opened buckets as `B`'s, its keys, its opened buckets' entries). -/
theorem txFacts_upd (W : WView) (T T' : WTx) (bl : Loc) (B B'' : BRec)
    (hB : T.bs !! bl = some B) (hT' : T'.bs = <[bl := B'']> T.bs)
    (hib : B''.ib = B.ib) (hbm : B''.bm = B.bm)
    (hrn : B''.bv.rootNode' = null → B.bv.rootNode' = null)
    (hent : ∀ k v, entryIn W B k v → entryIn W B'' k v) (hk : bktKeys W B'')
    (hf : ∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktNested W T B) :
    ∀ bl' C, T'.bs !! bl' = some C → bktKeys W C ∧ bktNested W T' C := by
  have hlk : ∀ y, T'.bs !! y = if y = bl then some B'' else T.bs !! y := by
    intro y; rw [hT']
    by_cases h : y = bl
    · subst h; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]
  -- an opened bucket's record in `T'`
  have htgt : ∀ c C0 (v : List w8), T.bs !! c = some C0 → C0.ib.root' = (ibOf v).root' →
      (C0.bv.rootNode' = null → C0.ib = ibOf v) →
      ∃ C', T'.bs !! c = some C' ∧ C'.ib.root' = (ibOf v).root' ∧
        (C'.bv.rootNode' = null → C'.ib = ibOf v) := by
    intro c C0 v h0 h1 h2
    rw [hlk]
    by_cases hc : c = bl
    · subst hc; rw [hB] at h0; cases h0
      exact ⟨B'', by rw [if_pos rfl], by rw [hib]; exact h1, fun h => by rw [hib]; exact h2 (hrn h)⟩
    · exact ⟨C0, by rw [if_neg hc]; exact h0, h1, h2⟩
  have hnest : ∀ C C2, (∀ k c, C2.bm !! k = some c → C.bm !! k = some c) →
      (∀ k v, entryIn W C k v → entryIn W C2 k v) → bktNested W T C → bktNested W T' C2 := by
    intro C C2 hm he hn k c hkc
    obtain ⟨C0, v, h0, h1, h2, h3, h4⟩ := hn k c (hm k c hkc)
    obtain ⟨C', h5, h6, h7⟩ := htgt c C0 v h0 h3 h4
    exact ⟨C', v, h5, he k v h1, h2, h6, h7⟩
  intro bl' C hC
  rw [hlk] at hC
  by_cases h : bl' = bl
  · rw [if_pos h] at hC; cases hC
    exact ⟨hk, hnest B B'' (fun k c h => by rw [← hbm]; exact h) hent (hf bl B hB).2⟩
  · rw [if_neg h] at hC
    exact ⟨(hf bl' C hC).1, hnest C C (fun _ _ h => h) (fun _ _ h => h) (hf bl' C hC).2⟩

/-- The shape of the transaction with the bucket `bl`'s record `B''` put back. -/
theorem txShape_close (γ : GName) (W : WView) (T T' : WTx) (bl : Loc) (B B'' : BRec)
    (hB : T.bs !! bl = some B) (hT' : T'.bs = <[bl := B'']> T.bs)
    (hib : B''.ib = B.ib) (hbm : B''.bm = B.bm)
    (hrn : B''.bv.rootNode' = null → B.bv.rootNode' = null)
    (hent : ∀ k v, entryIn W B k v → entryIn W B'' k v) (hk : bktKeys W B'') :
    txFrame (GF := GF) γ W T bl ∗ bktToks γ W B'' ⊢ txShape γ W T' := by
  unfold txFrame txShape
  iintro ⟨⟨%M, Ha, %Hd, Hback, %Hf⟩, Hb⟩
  iexists M
  iframe Ha
  isplitr
  · ipureintro; exact Hd
  isplitl
  · rw [hT']; iapply Hback $$ %B'' Hb
  · ipureintro; exact txFacts_upd W T T' bl B B'' hB hT' hib hbm hrn hent hk Hf

/-- The transaction's shape with the bucket `bl`'s record unchanged. -/
theorem txShape_same (γ : GName) (W : WView) (T T' : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) (hT' : T'.bs = <[bl := B]> T.bs) :
    txShape (GF := GF) γ W T ⊢ txShape γ W T' := by
  have h : T'.bs = T.bs := by rw [hT', GMap.insert_id _ _ _ hB]
  unfold txShape
  rw [h]
  have hn : ∀ C, bktNested W T' C ↔ bktNested W T C := by
    intro C; unfold bktNested; rw [h]
  simp only [hn]
  exact .rfl

end tx

section acc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A key a writer's cursor returned, with its bytes (`keySrcIs`), lent out (and back). -/
theorem keySrcIs_acc (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (k : GoSlice) (kbs : List w8) (hc : W.data.locCar ≠ 0)
    (h : keySrcIs W B k kbs) :
    wctx (GF := GF) W bl B txl pmap pm dqp ⊢ ∃ (dq : DFrac), k ↦*{dq} kbs ∗
      (k ↦*{dq} kbs -∗ wctx W bl B txl pmap pm dqp) := by
  iintro Hctx
  rcases h with ⟨rfl, rfl⟩ | ⟨l, r, i, it, w, hr, hit, hw, rfl, hns, rfl⟩ |
    ⟨pid, p, pg, off, n, hpa, hinl, hlen, hb, hn, rfl, rfl⟩
  · iexists DFrac.own 1
    isplitl []
    · iapply ownSlice_nil
    iintro -; iexact Hctx
  · unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    icases bktOwn_node_acc W bl B l r hr $$ Hb with ⟨Hn, Hback⟩
    isimp only [nodeOwn] at Hn
    icases Hn with ⟨Hn, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ it w => wOwn (GF := GF) W it w) hit hw $$ Hents
      with ⟨Hi, Hentsback⟩
    isimp only [wOwn] at Hi
    icases Hi with ⟨%Hfp, Hk, Hvv⟩
    icases srcBorrow W hc W.q it.key' w.ks w.key hns $$ [Hpv Hk] with ⟨%dq, -, Hk, Hkback⟩
    · iframe
    iexists dq
    iframe Hk
    iintro Hk
    ihave Hk := Hkback $$ Hk
    icases Hk with ⟨Hpv, Hk⟩
    ihave Hents := Hentsback $$ [Hk Hvv]
    · unfold wOwn; iframe; ipureintro; exact Hfp
    ihave Hb := Hback $$ %r [Hn Hins Hicap Hents Hch Hchcap Hkey]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B l r hr]
    iframe
    unfold wView; iframe; iframe #; ipureintro; exact Hlgv
  · unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    isimp only [bktOwn] at Hb
    icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    have Hne : pg ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    icases wpageAt_acc W B pid p pg hc hpa hinl Hne $$ [Hpv Hpo] with ⟨%dq, %Hc, Hpg, Hpgback⟩
    · iframe
    icases bytes_slice_acc (hG := hG) p dq pg off n hb hn Hc $$ Hpg with ⟨Hk, Hkback⟩
    iexists dq
    iframe Hk
    iintro Hk
    ihave Hpg := Hkback $$ Hk
    ihave Hpg := Hpgback $$ Hpg
    icases Hpg with ⟨Hpv, Hpo⟩
    unfold bktOwn wView; iframe; iframe #; ipureintro; exact Hlgv

end acc

end bbolt
end EtcdGrove
end Perennial
