/-
U7's (`notes/bbolt-proof-plan.md`) facts about a node's entries: the search index from
`sort.Search`'s result, `put`'s and `del`'s lists, and the inodes' ownership (`wOwn`) under them
(ported from `old/bbolt/.../NodeModel.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The search predicate of `put`/`del`: entry `i`'s key is not below `kb`. -/
def gePred (ws : List WEntry) (kb : List w8) (i : Int) : Bool :=
  decide (¬ go.GoStringLt (wKey ws i.toNat) kb)

theorem gePred_mono (ws : List WEntry) (kb : List w8) (hs : wsSorted ws) :
    sort.IsMonoPred (gePred ws kb) (ws.length : Int) := by
  intro i j hij hi
  simp only [gePred, decide_eq_true_eq] at hi ⊢
  intro hj
  apply hi
  have hlt := hs i.toNat j.toNat (by omega) (by omega)
  exact go.goStringLt_trans hlt hj

theorem wsIdx_of_bounds (ws : List WEntry) (kb : List w8) (idx : Nat) (hle : idx ≤ ws.length)
    (hbelow : ∀ k < idx, go.GoStringLt (wKey ws k) kb)
    (hat : idx < ws.length → ¬ go.GoStringLt (wKey ws idx) kb) : wsIdx ws kb = idx := by
  induction ws generalizing idx with
  | nil => simp at hle; subst hle; rfl
  | cons w ws ih =>
    cases idx with
    | zero =>
      have h0 := hat (by simp)
      simp only [wKey, List.getElem?_cons_zero, Option.map_some, Option.getD_some] at h0
      simp [wsIdx, h0]
    | succ idx =>
      have h0 := hbelow 0 (by omega)
      simp only [wKey, List.getElem?_cons_zero, Option.map_some, Option.getD_some] at h0
      have := ih idx (by simp at hle; omega)
        (fun k hk => by have := hbelow (k + 1) (by omega); simpa [wKey] using this)
        (fun hk => by have := hat (by simp; omega); simpa [wKey] using this)
      simp only [wsIdx] at this ⊢
      rw [List.takeWhile_cons_of_pos (by simpa using h0), List.length_cons, this]

theorem wsIdx_le (ws : List WEntry) (kb : List w8) : wsIdx ws kb ≤ ws.length := by
  unfold wsIdx; exact (List.takeWhile_sublist _).length_le

/-- `wsFound` by the key at the index. -/
theorem wsFound_iff (ws : List WEntry) (kb : List w8) :
    wsFound ws kb ↔ wsIdx ws kb < ws.length ∧ wKey ws (wsIdx ws kb) = kb := by
  unfold wsFound wKey
  constructor
  · intro h
    cases hx : ws[wsIdx ws kb]? with
    | none => rw [hx] at h; simp at h
    | some w =>
      rw [hx] at h
      simp only [Option.map_some, Option.some.injEq] at h
      refine ⟨(List.getElem?_eq_some_iff.mp hx).1, ?_⟩
      simp [h]
  · intro ⟨hl, hk⟩
    rw [List.getElem?_eq_getElem hl] at hk ⊢
    simpa using hk

/-- `put`'s entries: the entry at the index replaced (found) or inserted there. -/
theorem wsPutAt_eq (ws : List WEntry) (ok : List w8) (e : WEntry) :
    wsPutAt ws ok e = if wsFound ws ok then ws.set (wsIdx ws ok) e
      else ws.take (wsIdx ws ok) ++ e :: ws.drop (wsIdx ws ok) := by
  unfold wsPutAt
  split
  · rename_i h
    have hl := ((wsFound_iff ws ok).1 h).1
    rw [List.set_eq_take_append_cons_drop, if_pos hl]; simp
  · simp

/-- What `append(s, zero)` and then `copy(s[i+1:], s[i:])` leave (`wp_slice_copy_within`), with
element `i` then set to `x`: `x` inserted before element `i`. -/
theorem insert_copy_list {A : Type} (ins : List A) (z x : A) (i : Nat) (hi : i ≤ ins.length) :
    ((ins ++ [z]).take (i + 1) ++
        ((subslice i (ins.length + 1) (ins ++ [z])).take (ins.length + 1 - (i + 1)) ++
          (subslice (i + 1) (ins.length + 1) (ins ++ [z])).drop (ins.length + 1 - i)) ++
        (ins ++ [z]).drop (ins.length + 1)).set i x =
      ins.take i ++ x :: ins.drop i := by
  have h1 : subslice i (ins.length + 1) (ins ++ [z]) = (ins ++ [z]).drop i := by
    simp only [subslice]; rw [List.take_of_length_le (by simp)]
  have h2 : (subslice (i + 1) (ins.length + 1) (ins ++ [z])).drop (ins.length + 1 - i) = [] := by
    apply List.drop_of_length_le; simp [subslice]; omega
  have h3 : (ins ++ [z]).drop (ins.length + 1) = [] := List.drop_of_length_le (by simp)
  have h4 : ((ins ++ [z]).drop i).take (ins.length + 1 - (i + 1)) = ins.drop i := by
    rw [List.drop_append_of_le_length hi]
    exact List.take_left' (by simp)
  obtain ⟨y, hy⟩ : ∃ y, (ins ++ [z])[i]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
  have h5 : (ins ++ [z]).take (i + 1) = ins.take i ++ [y] := by
    rw [List.take_add_one, hy, List.take_append_of_le_length hi]; rfl
  rw [h1, h2, h3, h4, h5, List.append_nil, List.append_nil, List.append_assoc]
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left hi, Nat.sub_self, List.singleton_append,
    List.set_cons_zero]

end pure

section bi
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A live inode's ownership, unfolded. -/
theorem wOwn_live (v : View) (it : Inode) (w : WEntry) :
    wOwn (GF := GF) v true it w ⊣⊢ iprop(⌜it.flags' = w.flags ∧ it.pgid' = w.pgid⌝ ∗
      srcOwn v it.key' w.ks w.key ∗ srcOwn v it.value' w.vs w.value) := by
  unfold wOwn; simp only [↓reduceIte]; exact .rfl

/-- The inodes with an entry inserted at `i`. -/
theorem wOwns_insert (v : View) (ins : List Inode) (ws : List WEntry) (i : Nat) (x : Inode)
    (e : WEntry) (hlen : ins.length = ws.length) (hi : i ≤ ins.length) :
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) v true it w) ∗ wOwn v true x e ⊢
      [∗list] it;w ∈ ins.take i ++ x :: ins.drop i;ws.take i ++ e :: ws.drop i, wOwn v true it w := by
  have hs := (BigSepL2.bigSepL2_append (PROP := IProp GF) (Φ := fun _ it w => wOwn (GF := GF) v true it w)
    (l1a := ins.take i) (l1b := ins.drop i) (l2a := ws.take i) (l2b := ws.drop i)
    (Or.inl (by simp; omega)))
  have hs2 := (BigSepL2.bigSepL2_append (PROP := IProp GF) (Φ := fun _ it w => wOwn (GF := GF) v true it w)
    (l1a := ins.take i) (l1b := x :: ins.drop i) (l2a := ws.take i) (l2b := e :: ws.drop i)
    (Or.inl (by simp; omega)))
  rw [List.take_append_drop, List.take_append_drop] at hs
  iintro ⟨H, Hx⟩
  icases hs.1 $$ H with ⟨H1, H2⟩
  iapply hs2.2
  iframe H1
  iapply BigSepL2.bigSepL2_cons.2
  iframe

/-- The inodes with entry `i` replaced. -/
theorem wOwns_set (v : View) (ins : List Inode) (ws : List WEntry) (i : Nat) (x : Inode)
    (e : WEntry) (hlen : ins.length = ws.length) (hi : i < ins.length) :
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) v true it w) ∗ wOwn v true x e ⊢
      [∗list] it;w ∈ ins.set i x;ws.set i e, wOwn v true it w := by
  iintro ⟨H, Hx⟩
  icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ it w => wOwn (GF := GF) v true it w)
    (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (show i < ws.length by omega))) $$ H
    with ⟨-, Hback⟩
  iapply Hback
  iexact Hx

/-- The inodes with entry `i` removed. -/
theorem wOwns_delete (v : View) (ins : List Inode) (ws : List WEntry) (i : Nat)
    (hlen : ins.length = ws.length) (hi : i < ins.length) :
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) v true it w) ⊢
      [∗list] it;w ∈ ins.take i ++ ins.drop (i + 1);ws.take i ++ ws.drop (i + 1), wOwn v true it w := by
  have hs := (BigSepL2.bigSepL2_append (PROP := IProp GF) (Φ := fun _ it w => wOwn (GF := GF) v true it w)
    (l1a := ins.take i) (l1b := ins.drop i) (l2a := ws.take i) (l2b := ws.drop i)
    (Or.inl (by simp; omega)))
  have hs2 := (BigSepL2.bigSepL2_append (PROP := IProp GF) (Φ := fun _ it w => wOwn (GF := GF) v true it w)
    (l1a := ins.take i) (l1b := ins.drop (i + 1)) (l2a := ws.take i) (l2b := ws.drop (i + 1))
    (Or.inl (by simp; omega)))
  rw [List.take_append_drop, List.take_append_drop] at hs
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons (show i < ws.length by omega)] at hs
  iintro H
  icases hs.1 $$ H with ⟨H1, H2⟩
  icases BigSepL2.bigSepL2_cons.1 $$ H2 with ⟨-, H2⟩
  iapply hs2.2
  iframe

end bi

end Write

end bbolt
end EtcdGrove
end Perennial
