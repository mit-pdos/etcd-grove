/-
The writer's opened buckets, well-formedness (U6e, `notes/bbolt-proof-plan.md`): opening a nested
bucket (`bktOpened`'s state, `WX.addBkt` over the parent's cache update) keeps `wOK` and the
writer's data.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Read.WOpenOK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WOpen

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wok
variable [GooseExts]

/-! ### A bucket record whose cache grows -/

/-- `B` with the cache `bm`, which has every entry of `B`'s. -/
def bmGrow (B : BRec) (bm : GMap GoString Loc) : Prop :=
  ∀ k c, B.bm !! k = some c → bm !! k = some c

theorem bmGrow_isSome (B : BRec) (bm : GMap GoString Loc) (h : bmGrow B bm) (k : List w8)
    (hn : (bm !! k).isSome = false) : (B.bm !! k).isSome = false := by
  cases e : B.bm !! k with
  | none => rfl
  | some c => rw [h k c e] at hn; cases hn

theorem nodeClean_bm (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (bm : GMap GoString Loc)
    (h : bmGrow B bm) (l : Loc) (r : NRec) (hn : nodeClean v hwm bl B l r) :
    nodeClean v hwm bl { B with bm := bm } l r := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩ := hn
  exact ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11,
    fun hl w hw hf => ⟨fun hs => (n12 hl w hw hf).1 (bmGrow_isSome B bm h _ hs), (n12 hl w hw hf).2⟩,
    n13, n14, n15, n16, n17⟩

theorem bktClean_bm (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (bm : GMap GoString Loc)
    (h : bmGrow B bm) (hc : bktClean v hwm bl B) : bktClean v hwm bl { B with bm := bm } := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  exact ⟨c1, c2, c3, c4, c5, c6, c7, fun l r hr => nodeClean_bm v hwm bl B bm h l r (c8 l r hr), c9, c10⟩

theorem bktKeys_bm (v : View) (B : BRec) (bm : GMap GoString Loc) (h : bmGrow B bm)
    (hk : bktKeys v B) : bktKeys v { B with bm := bm } := by
  obtain ⟨bnd, k1, k2, k3⟩ := hk
  refine ⟨bnd, k1, k2, fun l r hr => ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := k3 l r hr
  refine ⟨m1, m2, m3, m4, m5, fun hl w hw hf hroot hno => m6 hl w hw hf hroot fun ho => hno ?_⟩
  unfold opened at ho ⊢
  cases e : B.bm !! w.key with
  | none => rw [e] at ho; cases ho
  | some c => simp only at ho ⊢; rw [h _ c e]; rfl

theorem entryIn_bm (vw : View) (B : BRec) (bm : GMap GoString Loc) (k v : List w8) :
    entryIn vw { B with bm := bm } k v ↔ entryIn vw B k v := Iff.rfl

/-! ### The opened state -/

section opened
variable (X : WX) (bl c : Loc) (B C : BRec) (nb : List w8) (h : GoString × Nat)

/-- The state after the open. -/
abbrev XO : WX := (X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C h

theorem XO_bs (k : Loc) : (XO X bl c B C nb h).t.bs !! k =
    if k = c then some C else if k = bl then some { B with bm := B.bm.insert nb c }
    else X.t.bs !! k := by
  unfold XO
  rw [addBkt_bs]
  split
  · rfl
  · unfold WX.setBkt
    split
    · rename_i hk; subst hk; simp
    · rename_i hk; exact GMap.lookup_insert_ne _ _ (Ne.symm hk)

variable (hB : X.t.bs !! bl = some B) (hc : X.t.bs !! c = none) (hbm : B.bm !! nb = none)
include hB hc hbm

omit hbm in
theorem c_ne_bl : c ≠ bl := by intro e; subst e; rw [hB] at hc; cases hc

/-- A bucket of the opened state: the new one, or an old one with (maybe) a grown cache. -/
theorem XO_back (k : Loc) (D : BRec) (hD : (XO X bl c B C nb h).t.bs !! k = some D) :
    (k = c ∧ D = C) ∨ (k ≠ c ∧ ∃ D0, X.t.bs !! k = some D0 ∧ D = { D0 with bm := D.bm } ∧
      bmGrow D0 D.bm ∧ (k ≠ bl → D = D0)) := by
  rw [XO_bs] at hD
  by_cases hkc : k = c
  · simp only [hkc, ↓reduceIte, Option.some.injEq] at hD; exact Or.inl ⟨hkc, hD.symm⟩
  · right
    simp only [hkc, ↓reduceIte] at hD
    refine ⟨hkc, ?_⟩
    by_cases hkb : k = bl
    · simp only [hkb, ↓reduceIte, Option.some.injEq] at hD
      subst hkb hD
      refine ⟨B, hB, rfl, ?_, fun h' => absurd rfl h'⟩
      intro k' c' e
      by_cases hk' : nb = k'
      · subst hk'
        rw [hbm] at e; cases e
      · rw [GMap.lookup_insert_ne _ _ hk']; exact e
    · simp only [hkb, ↓reduceIte] at hD
      exact ⟨D, hD, rfl, fun _ _ e => e, fun _ => rfl⟩

end opened


/-- **Opening a nested bucket keeps `wOK` and the data**: the parent `bl`'s cache gains
`nb ↦ c`, the fresh bucket `c` (record `C`, `openedRec` of the entry's value) is added, live, a
handle. -/
theorem wOK_bktOpened (X : WX) (bl c : Loc) (B C : BRec) (w : WEntry) (nb : List w8) (g : Nat)
    (hok : wOK X) (hB : X.t.bs !! bl = some B) (hw : w ∈ X.allEnts bl) (hk : w.key = nb)
    (hf : isBktFlag w.flags) (hbm : B.bm !! nb = none) (hbo : X.t.bobjs !! c = none)
    (hrec : openedRec B.bv.tx' w.value w.vs C)
    (hbv : bvalOK X.v.pages X.t.mv.pgid'.toNat w.value) (hent : entryIn X.v B nb w.value)
    (htk : inBucketRoot w.value ≠ 0 → treeKeys X.v.pages (inBucketRoot w.value) none none) :
    wOK ((X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C (nb, g)) ∧
      wtxData ((X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C (nb, g)) = wtxData X := by
  sorry

end wok

end WOpen

end bbolt
end EtcdGrove
end Perennial
