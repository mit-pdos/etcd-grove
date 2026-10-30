/-
`Bucket.spill`'s put of an opened child bucket's new value into the leaf holding its entry
(`node.put(name, name, value, 0, BucketLeafFlag)`): `ShapeLeaf.lean`'s lemmas for a leaf whose
entries `A ++ D ++ C` become `A ++ E ++ C`, where `D` and `E` may be nested buckets' entries,
if of opened buckets (whose trees the bucket's tokens do not hold: `nodeToks`).

- `bktToks_leafOpX`: the tokens stay;
- `bktKeysB_leafOpX`: the keys stay a B+tree's, if a nested bucket's entry put has its root's
  keys over the view (`nodeKeys`' last clause; for an inline value, nothing);
- `entryIn_leafOpX`: the nested buckets' entries of other keys stay, and the entry put is one.
-/
module

public import Proof.go_etcd_io.bbolt.ShapeLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The leaf's record changed, the entries put within its bounds, a nested bucket's with its
root's keys: the keys stay a B+tree's. -/
theorem bktKeysB_leafOpX (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB W B bnd)
    (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, keyIn (bnd l).1 (bnd l).2 w.key ∧ (isBktFlag w.flags →
      inBucketRoot w.value ≠ 0 → treeKeys W.pages (inBucketRoot w.value) none none))
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
      · exact fun h0 _ => (hE w h).2 hb h0
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

/-- The leaf's record changed, the nested buckets' entries removed not of the key `k`: the
nested buckets' entries of `k` stay. -/
theorem entryIn_leafOpX (W : WView) (B : BRec) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true)
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (k v : List w8) (hD : ∀ w ∈ D, isBktFlag w.flags → w.key ≠ k) (h : entryIn W B k v) :
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
        · exact absurd hk (hD w h hb)
        · exact Or.inr h
      exact ⟨y, r', w, by show (<[y := r']> B.ns) !! y = _; rw [GMap.lookup_insert], e1, hw', hk, hb, hv⟩
    · exact ⟨y, ry, w, by show (<[l := r']> B.ns) !! y = _; rw [ns_insert_lookup, if_neg hyl]; exact hy,
        hl, hw, hk, hb, hv⟩
  · right
    exact ⟨c, p, pg, i, (posRoot_leafOp B l r r' hr hleaf e1 c).2 hc, hrest⟩

/-- The entry put, a nested bucket's, is one of the leaf's. -/
theorem entryIn_put (W : WView) (B : BRec) (l : Loc) (r' : NRec) (e1 : r'.nv.isLeaf' = true)
    (w : WEntry) (hw : w ∈ r'.ws) (hb : isBktFlag w.flags) :
    entryIn W { B with ns := <[l := r']> B.ns } w.key w.value :=
  Or.inl ⟨l, r', w, by show (<[l := r']> B.ns) !! l = _; rw [GMap.lookup_insert], e1, hw, rfl, hb,
    rfl⟩

end pure

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

theorem nodeToks_leafOpX (γ : GName) (W : WView) (B : BRec) (r r' : NRec)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (e3 : r'.nv.pgid' = r.nv.pgid')
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, isBktFlag w.flags → opened B w.key) :
    nodeToks γ W B r ⊢ nodeToks γ W B r' := by
  unfold nodeToks
  rw [e3, e1, hleaf, hws, hws']
  iintro ⟨Hp, Hl⟩
  iframe Hp
  iapply bigSepL_mid _ A D C E ?_ $$ Hl
  intro w hw
  by_cases hb : isBktFlag w.flags
  · have ho := hE w hw hb
    simp only [↓reduceIte, ho, not_true_eq_false, and_false]
    exact .rfl
  · simp only [↓reduceIte, hb, false_and]
    exact .rfl

/-- The leaf's record changed, the entries put not of unopened nested buckets: the bucket's
tokens stay. -/
theorem bktToks_leafOpX (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (e3 : r'.nv.pgid' = r.nv.pgid')
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, isBktFlag w.flags → opened B w.key) :
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
  ihave Hn := nodeToks_leafOpX γ W B r r' hleaf e1 e3 A D C E hws hws' hE $$ Hn
  iapply Hback $$ %r' Hn

end toks

end bbolt
end EtcdGrove
end Perennial
