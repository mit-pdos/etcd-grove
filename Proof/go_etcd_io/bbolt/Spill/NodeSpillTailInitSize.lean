/-
`node.spill` after its children's loop (U9w, `notes/bbolt-proof-plan.md`; pure): **a piece's size
facts** from its entries: under `insLens`, a node's size is its entries' (`insSize_ws`), its page
body's length that size less the header (`body_insSize`); the inodes' lengths of a piece, cut from
the node's (`insLens_cut`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section size
variable [GooseExts]

/-- An entry's share of a node's size. -/
def wSz (w : WEntry) : Nat := 16 + w.key.length + w.value.length

theorem insLens_cons {it : Inode} {ins : List Inode} {w : WEntry} {ws : List WEntry}
    (h : insLens (it :: ins) (w :: ws)) :
    (it.key'.len.toNat = w.key.length ∧ it.value'.len.toNat = w.value.length) ∧ insLens ins ws :=
  ⟨h 0 it w rfl rfl, fun k a b ha hb => h (k + 1) a b ha hb⟩

/-- **A node's size is its entries'.** -/
theorem insSize_ws : ∀ (ins : List Inode) (ws : List WEntry), insLens ins ws →
    ins.length = ws.length → insSize ins = 16 + (ws.map wSz).sum
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | it :: ins, w :: ws, hl, hn => by
    obtain ⟨⟨h1, h2⟩, hr⟩ := insLens_cons hl
    have ih := insSize_ws ins ws hr (by simpa using hn)
    unfold insSize at ih ⊢
    simp only [List.map_cons, List.sum_cons, wSz] at ih ⊢
    omega

theorem dataBytes_length_ws (ws : List WEntry) :
    (dataBytes (wsMs ws)).length = (ws.map fun w => w.key.length + w.value.length).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wsMs, List.map_cons, dataBytes, List.flatMap_cons, List.length_append,
      List.sum_cons] at ih ⊢
    rw [ih]; simp [InodeM.kv]

theorem sum_wSz (ws : List WEntry) :
    (ws.map wSz).sum = 16 * ws.length + (ws.map fun w => w.key.length + w.value.length).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, List.sum_cons, List.length_cons, wSz] at ih ⊢; omega

/-- **A page body's length** is the entries' size less the header. -/
theorem body_ws (ws : List WEntry) :
    16 + (pageBody true (wsMs ws)).length = 16 + (ws.map wSz).sum := by
  rw [pageBody_length, dataBytes_length_ws, sum_wSz]
  simp [wsMs]

/-- `insSize` depends only on the entries' data. -/
theorem sum_wSz_congr {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) :
    (ws'.map wSz).sum = (ws.map wSz).sum := by
  have : ws'.map wSz = ws.map wSz := by
    have e1 : ws'.map wSz = (ws'.map wDat).map (fun d => 16 + d.2.2.1.length + d.2.2.2.length) := by
      simp [wSz, wDat, Function.comp_def]
    have e2 : ws.map wSz = (ws.map wDat).map (fun d => 16 + d.2.2.1.length + d.2.2.2.length) := by
      simp [wSz, wDat, Function.comp_def]
    rw [e1, e2, h]
  rw [this]

/-- **The inodes' lengths of each piece** (the pieces cut at the same lengths). -/
theorem insLens_cut : ∀ (A : List (List Inode)) (W : List (List WEntry)),
    A.length = W.length → (∀ (k : Nat) (a : List Inode) (w : List WEntry), A[k]? = some a →
      W[k]? = some w → a.length = w.length) →
    insLens A.flatten W.flatten →
    ∀ (k : Nat) (a : List Inode) (w : List WEntry), A[k]? = some a → W[k]? = some w → insLens a w
  | [], _, _, _, _, k, a, w, ha, _ => by simp at ha
  | _ :: _, [], hl, _, _, _, _, _, _, _ => by simp at hl
  | a0 :: A, w0 :: W, hl, hlen, hL, k, a, w, ha, hw => by
    have h0 := hlen 0 a0 w0 rfl rfl
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hw
      subst ha hw
      intro m it e hit he
      have hm : m < a0.length := (List.getElem?_eq_some_iff.1 hit).1
      exact hL m it e (by rw [List.flatten_cons, List.getElem?_append_left hm]; exact hit)
        (by rw [List.flatten_cons, List.getElem?_append_left (by omega)]; exact he)
    | succ k =>
      simp only [List.getElem?_cons_succ] at ha hw
      refine insLens_cut A W (by simpa using hl) (fun k a w ha hw => hlen (k + 1) a w ha hw) ?_ k a w ha hw
      intro m it e hit he
      have := hL (a0.length + m) it e
        (by rw [List.flatten_cons, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hit)
        (by rw [List.flatten_cons, List.getElem?_append_right (by omega), h0, Nat.add_sub_cancel_left]; exact he)
      exact this

end size

end Spill

end bbolt
end EtcdGrove
end Perennial
