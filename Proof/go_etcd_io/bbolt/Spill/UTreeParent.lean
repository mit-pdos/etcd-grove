/-
The spill's pure tree facts (U9f, `notes/bbolt-proof-plan.md`): **the parent of a spilled child**.
An unspilled branch's facts (`uBr`, `uTree.branch`'s premises) for its entries' descriptors `es`;
after child `c` of entry `j` is spilled (`node.spill`'s child case: the pieces put in the parent,
`parentSpilled`), the parent's branch facts hold again, entry `j`'s descriptor replaced by the
pieces' finished ones (`uBr_replace`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTreeBnd
public import Proof.go_etcd_io.bbolt.Spill.NodeSpec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section parent
variable [GooseExts]

/-- **An unspilled branch's facts** (`uTree.branch`'s premises), its entries' descriptors `es`. -/
structure uBr (X : WX) (bl : Loc) (P : Pages) (hwm : Nat) (n : Loc) (r : NRec)
    (lo hi : Option (List w8)) (h : Nat) (es : List UE) : Prop where
  node : X.node bl n = some r
  un : uNode X bl n r lo hi
  leaf : r.nv.isLeaf' = false
  two : 2 ≤ r.ws.length
  len : es.length = r.ws.length
  ent : ∀ i w e, r.ws[i]? = some w → es[i]? = some e →
    uEnt X bl P hwm n lo hi r.ws r.cs h i w e
  chnd : (es.filterMap UE.ch).Nodup
  cs : ∀ c ∈ r.cs, (∃ e ∈ es, e.ch = some c) ∨ spilledN X bl c
  csnd : r.cs.Nodup
  Nnd : (n :: es.flatMap UE.N).Nodup
  pg0 : r.nv.pgid' = W64 0 → ∀ e ∈ es, e.ch = none

theorem uTree_of_uBr {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {r : NRec}
    {lo hi : Option (List w8)} {h : Nat} {es : List UE} (hb : uBr X bl P hwm n r lo hi h es) :
    uTree X bl P hwm n lo hi (h + 1) (ownF r.nv.pgid' ++ es.flatMap UE.F)
      (ownSl X.v r.nv.pgid' ++ es.flatMap UE.D) (n :: es.flatMap UE.N) (es.flatMap UE.E) :=
  uTree.branch n r lo hi h es hb.node hb.un hb.leaf hb.two hb.len hb.ent hb.chnd hb.cs hb.csnd
    hb.Nnd hb.pg0

theorem uBr_of_uTree {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {r : NRec}
    {lo hi : Option (List w8)} {h' : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h' F D N E) (hr : X.node bl n = some r)
    (hl : r.nv.isLeaf' = false) :
    ∃ h es, h' = h + 1 ∧ F = ownF r.nv.pgid' ++ es.flatMap UE.F ∧
      D = ownSl X.v r.nv.pgid' ++ es.flatMap UE.D ∧ N = n :: es.flatMap UE.N ∧
      E = es.flatMap UE.E ∧ uBr X bl P hwm n r lo hi h es := by
  cases hu with
  | leaf _ r' _ _ _ hr' _ hleaf =>
    rw [hr] at hr'; cases hr'; rw [hleaf] at hl; cases hl
  | branch _ r' _ _ h es hr' hun hleaf h2 hlen hent hchnd hcs hcsnd hNnd hpg0 =>
    rw [hr] at hr'; cases hr'
    exact ⟨h, es, rfl, rfl, rfl, rfl, rfl, ⟨hr, hun, hleaf, h2, hlen, hent, hchnd, hcs, hcsnd, hNnd,
      hpg0⟩⟩

/-- A finished subtree's first key is below its upper bound. -/
theorem fTree_keyLt {P : Pages} {hwm id : Nat} {k : List w8} {hi : Option (List w8)} {h : Nat}
    {S : List Nat} {E : List El} (hf : fTree P hwm id k hi h S E) : keyLt k hi := by
  obtain ⟨hs, ⟨pg, hpg, hc, hk⟩, -⟩ := hf
  have hkeys := hs.keys
  cases hkeys with
  | leaf _ pg' _ _ hpg' hfl hks _ =>
    rw [hpg] at hpg'; cases hpg'
    have H := hks 0 hc
    unfold pageKey at hk
    rw [if_pos (by rw [hfl]; rfl)] at hk
    rw [hk] at H; exact H.2
  | branch _ pg' _ _ _ hpg' hfl _ hks _ _ =>
    rw [hpg] at hpg'; cases hpg'
    have H := hks 0 hc
    unfold pageKey at hk
    rw [if_neg (by rw [hfl]; decide)] at hk
    rw [hk] at H; exact H.2

/-- **The transport of an entry** to another state through a spill step's frame, at another
index of other entries (by data the same entry), within looser bounds, other children. -/
theorem uEnt_move {X X' : WX} {bl : Loc} {P P' : Pages} {hwm hwm' : Nat} {T : List Loc}
    (hfr : spFrame X X' bl T) (hh : hwm ≤ hwm') {n : Loc} {lo hi : Option (List w8)}
    {ws : List WEntry} {cs : List Loc} {h i : Nat} {w : WEntry} {e : UE}
    (he : uEnt X bl P hwm n lo hi ws cs h i w e) (hP : ∀ x ∈ e.D, P' !! x = P !! x)
    (hT : ∀ l ∈ T, l ∉ e.N ∧ ¬ spilledN X bl l) {lo' hi' : Option (List w8)}
    {ws' : List WEntry} {cs' : List Loc} {i' : Nat} {w' : WEntry} (hw : wDat w' = wDat w)
    (hcs : ∀ c ∈ cs, c ∈ cs')
    (hb : bndIn (childLo lo (wKey ws) i, childHi hi (wKey ws) ws.length i)
      (childLo lo' (wKey ws') i', childHi hi' (wKey ws') ws'.length i')) :
    uEnt X' bl P' hwm' n lo' hi' ws' cs' h i' w' e := by
  cases he with
  | child _ _ _ _ _ _ _ _ c rc F D N E hc hrc hpar hpg hkey hk' hne hut =>
    have hcT : c ∉ T := fun hm => (hT c hm).1 (uTree_head hut)
    obtain ⟨rc', hrc', hs, -⟩ := spFrame_node hfr hrc hcT
    have H := uTree_frame hfr hh hut hP hT
    exact uEnt.child _ _ _ _ _ _ _ _ c rc' F D N E (hcs c hc) hrc'
      (by rw [nodeSim_parent hs]; exact hpar) (by rw [nodeSim_pgid hs, wDat_pgid hw]; exact hpg)
      (by rw [hs.2.2.2.2.2.1, wDat_key hw]; exact hkey) (fun h0 => hk' (hs.2.1.1 h0))
      (by rw [length_of_dat hs.2.2.1]; exact hne) (uTree_bnd H _ _ hb)
  | fin _ _ _ _ _ _ _ _ S E hf =>
    obtain ⟨hf', he⟩ := fTree_agree hP hh hf
    have H := uEnt.fin (X := X') (bl := bl) (P := P') (hwm := hwm') n lo' hi' ws' cs' h i' w' S E
      (by rw [wDat_pgid hw, wDat_key hw]; exact fTree_bnd hb.2 hf')
    rw [he] at H; exact H

/-! ## The parent's entries after the splice -/

section splice
variable {ws ws' : List WEntry} {ps : List Piece} {j : Nat}

theorem splice_length
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) : ws'.length = ws.length + ps.length - 1 := by
  have := congrArg List.length hd
  simp only [List.length_map, List.length_append, List.length_take, List.length_drop] at this
  omega

theorem splice_lt
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) {i : Nat} (hi : i < j) :
    ∃ w' w, ws'[i]? = some w' ∧ ws[i]? = some w ∧ wDat w' = wDat w := by
  have H := congrArg (·[i]?) hd
  simp only [List.getElem?_map] at H
  rw [List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_map,
    List.getElem?_take_of_lt hi] at H
  have hw : i < ws.length := by omega
  rw [List.getElem?_eq_getElem hw] at H
  cases h' : ws'[i]? with
  | none => rw [h'] at H; cases H
  | some w' =>
    rw [h'] at H
    exact ⟨w', ws[i], rfl, List.getElem?_eq_getElem hw, Option.some.inj H⟩

theorem splice_mid
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) {k : Nat} (hk : k < ps.length) :
    ∃ w' x, ws'[j + k]? = some w' ∧ ps[k]? = some x ∧ wDat w' = pcDat x := by
  have H := congrArg (·[j + k]?) hd
  simp only [List.getElem?_map] at H
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp; omega)] at H
  simp only [List.length_map, List.length_take] at H
  rw [show j + k - min j ws.length = k by omega, List.getElem?_map,
    List.getElem?_eq_getElem hk] at H
  cases h' : ws'[j + k]? with
  | none => rw [h'] at H; cases H
  | some w' =>
    rw [h'] at H
    exact ⟨w', ps[k], rfl, List.getElem?_eq_getElem hk, Option.some.inj H⟩

theorem splice_hi
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) {k : Nat} (hjk : j < k) (hk : k < ws.length) :
    ∃ w' w, ws'[k + ps.length - 1]? = some w' ∧ ws[k]? = some w ∧ wDat w' = wDat w := by
  have H := congrArg (·[k + ps.length - 1]?) hd
  simp only [List.getElem?_map] at H
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega)] at H
  simp only [List.length_map, List.length_take] at H
  rw [show k + ps.length - 1 - min j ws.length - ps.length = k - (j + 1) by omega,
    List.getElem?_map, List.getElem?_drop, show j + 1 + (k - (j + 1)) = k by omega,
    List.getElem?_eq_getElem hk] at H
  cases h' : ws'[k + ps.length - 1]? with
  | none => rw [h'] at H; cases H
  | some w' =>
    rw [h'] at H
    exact ⟨w', ws[k], rfl, List.getElem?_eq_getElem hk, Option.some.inj H⟩

end splice

theorem wKey_of_get {ws : List WEntry} {i : Nat} {w : WEntry} (h : ws[i]? = some w) :
    wKey ws i = w.key := by
  unfold wKey; rw [h]; rfl

theorem pcKey_of_get {ps : List Piece} {i : Nat} {x : Piece} (h : ps[i]? = some x) :
    pcKey ps i = x.k := by
  unfold pcKey; rw [h]; rfl

end parent

end Spill

end bbolt
end EtcdGrove
end Perennial
