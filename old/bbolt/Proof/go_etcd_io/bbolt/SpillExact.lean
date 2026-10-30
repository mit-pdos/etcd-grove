/-
After `rebalance`, the keys of a bucket are `rblKeysB` (`RebalanceDefs.lean`: each node's
bounds inside its position's). With the node graph a tree (`bktRanked`), the positions' exact
bounds, computed down from the root (`exactBnd`), are bounds of the exact form (`bktKeysB`), so
the write path's specs over `bktShape` (the cursor's `seek` and `node`, which `Bucket.spill`
calls) apply again: `bktKeys_of_rbl`.
-/
module

public import Proof.go_etcd_io.bbolt.SpillKeys
public import Proof.go_etcd_io.bbolt.RebalanceDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-! ### Bounds inside bounds -/

theorem bndIn_transX (a b c : Option (List w8) × Option (List w8)) (h1 : bndIn a b)
    (h2 : bndIn b c) : bndIn a c := by
  unfold bndIn at *
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨x', hx', hn'⟩ := h2.1 y hy
    obtain ⟨x, hx, hn⟩ := h1.1 x' hx'
    exact ⟨x, hx, notLt_trans hn hn'⟩
  · obtain ⟨x', hx', hn'⟩ := h2.2 y hy
    obtain ⟨x, hx, hn⟩ := h1.2 x' hx'
    exact ⟨x, hx, notLt_trans hn' hn⟩

theorem bndIn_none (a : Option (List w8) × Option (List w8)) : bndIn a (none, none) := by
  unfold bndIn
  exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem bndIn_childX (a b : Option (List w8) × Option (List w8)) (ks : Nat → List w8) (n i : Nat)
    (h : bndIn a b) :
    bndIn (childLo a.1 ks i, childHi a.2 ks n i) (childLo b.1 ks i, childHi b.2 ks n i) := by
  unfold bndIn at *
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · unfold childLo at hy ⊢
    split
    · rename_i h0; rw [if_pos h0] at hy; exact h.1 y hy
    · rename_i h0; rw [if_neg h0] at hy; cases hy
      exact ⟨_, rfl, goStringLt_irrefl_r _⟩
  · unfold childHi at hy ⊢
    split
    · rename_i h0; rw [if_pos h0] at hy; cases hy
      exact ⟨_, rfl, goStringLt_irrefl_r _⟩
    · rename_i h0; rw [if_neg h0] at hy; exact h.2 y hy

theorem lt_notLt {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : ¬ go.GoStringLt c b) :
    go.GoStringLt a c := by
  rcases goStringLt_trichot_r a c with h | h | h
  · exact h
  · subst h; exact absurd h1 h2
  · exact absurd (goStringLt_trans h h1) h2

theorem keyIn_bndInX (a b : Option (List w8) × Option (List w8)) (k : List w8)
    (hk : keyIn a.1 a.2 k) (h : bndIn a b) : keyIn b.1 b.2 k := by
  unfold bndIn at h
  unfold keyIn keyGe keyLt at *
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx, hn⟩ := h.1 y hy
    exact notLt_trans (hk.1 x hx) hn
  · obtain ⟨x, hx, hn⟩ := h.2 y hy
    exact lt_notLt (hk.2 x hx) hn

theorem treeKeys_bndIn (P : GMap Nat (List w8)) (x : Nat) (lo hi lo' hi' : Option (List w8))
    (h : treeKeys P x lo hi) (hb : bndIn (lo, hi) (lo', hi')) : treeKeys P x lo' hi' := by
  induction h generalizing lo' hi' with
  | leaf root pg lo hi hpg hl hk hn =>
    exact .leaf root pg lo' hi' hpg hl (fun j hj => keyIn_bndInX (lo, hi) (lo', hi') _ (hk j hj) hb) hn
  | branch root pg lo hi kind hpg hb2 hn hk hc hch ih =>
    refine .branch root pg lo' hi' kind hpg hb2 hn
      (fun j hj => keyIn_bndInX (lo, hi) (lo', hi') _ (hk j hj) hb) hc (fun j hj => ?_)
    exact ih j hj _ _ (bndIn_childX (lo, hi) (lo', hi') (branchKey pg) (pageCount pg) j hb)

/-! ### The exact bounds -/

open Classical in
/-- The index of the entry of `ws` whose child is `g` (0 if none). -/
def pickIdx (ws : List WEntry) (g : w64) : Nat :=
  if h : ∃ (i : Nat) (w : WEntry), ws[i]? = some w ∧ w.pgid = g then Classical.choose h else 0

theorem pickIdx_eq (ws : List WEntry) (g : w64) (hnd : (ws.map WEntry.pgid).Nodup) (i : Nat)
    (w : WEntry) (hi : ws[i]? = some w) (hg : w.pgid = g) : pickIdx ws g = i := by
  have hex : ∃ (i : Nat) (w : WEntry), ws[i]? = some w ∧ w.pgid = g := ⟨i, w, hi, hg⟩
  unfold pickIdx
  rw [dif_pos hex]
  obtain ⟨w', hw', hg'⟩ := Classical.choose_spec hex
  exact pgid_idx_eq ws hnd i _ w w' hi hw' (hg'.trans hg.symm)

/-- The positions' bounds, `n` steps up at most (see the module doc). -/
def exactBndF (ns : GMap Loc NRec) : Nat → Loc → Option (List w8) × Option (List w8)
  | 0, _ => (none, none)
  | n + 1, l =>
    match ns !! l with
    | none => (none, none)
    | some r =>
      if r.nv.parent' = null then (none, none) else
      match ns !! r.nv.parent' with
      | none => (none, none)
      | some rp => entryBnd (exactBndF ns n r.nv.parent') rp.ws (pickIdx rp.ws r.nv.pgid')

theorem exactBndF_stable (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat)
    (hr : ∀ l r, ns !! l = some r → rk l ≤ N ∧ (r.nv.parent' ≠ null → rk l < rk r.nv.parent'))
    (hp : ∀ l r, ns !! l = some r → r.nv.parent' ≠ null → (ns !! r.nv.parent').isSome) :
    ∀ n m l, N + 1 - rk l ≤ n → N + 1 - rk l ≤ m → exactBndF ns n l = exactBndF ns m l := by
  intro n
  induction n with
  | zero =>
    intro m l hn hm
    cases h : ns !! l with
    | none =>
      cases m with
      | zero => rfl
      | succ m => simp [exactBndF, h]
    | some r => have := (hr l r h).1; omega
  | succ n ih =>
    intro m l hn hm
    cases m with
    | zero =>
      cases h : ns !! l with
      | none => simp [exactBndF, h]
      | some r => have := (hr l r h).1; omega
    | succ m =>
      simp only [exactBndF]
      cases h : ns !! l with
      | none => rfl
      | some r =>
        simp only
        by_cases h0 : r.nv.parent' = null
        · simp [h0]
        · simp only [h0, if_false]
          obtain ⟨rp, hrp⟩ := Option.isSome_iff_exists.1 (hp l r h h0)
          rw [hrp]
          simp only
          have h1 := (hr l r h).2 h0
          have h2 := (hr _ rp hrp).1
          rw [ih m _ (by omega) (by omega)]

/-- The positions' exact bounds. -/
def exactBnd (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (l : Loc) :
    Option (List w8) × Option (List w8) :=
  exactBndF ns (N + 1 - rk l) l

theorem exactBnd_root (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat) (l : Loc) (r : NRec)
    (hr : rk l ≤ N) (h : ns !! l = some r) (h0 : r.nv.parent' = null) :
    exactBnd ns rk N l = (none, none) := by
  unfold exactBnd
  obtain ⟨k, hk⟩ : ∃ k, N + 1 - rk l = k + 1 := ⟨N - rk l, by omega⟩
  rw [hk]; simp [exactBndF, h, h0]

theorem exactBnd_child (ns : GMap Loc NRec) (rk : Loc → Nat) (N : Nat)
    (hr : ∀ l r, ns !! l = some r → rk l ≤ N ∧ (r.nv.parent' ≠ null → rk l < rk r.nv.parent'))
    (hp : ∀ l r, ns !! l = some r → r.nv.parent' ≠ null → (ns !! r.nv.parent').isSome)
    (l : Loc) (r : NRec) (rp : NRec) (h : ns !! l = some r) (h0 : r.nv.parent' ≠ null)
    (hrp : ns !! r.nv.parent' = some rp) :
    exactBnd ns rk N l =
      entryBnd (exactBnd ns rk N r.nv.parent') rp.ws (pickIdx rp.ws r.nv.pgid') := by
  have h1 := (hr l r h).2 h0
  have h2 := (hr _ rp hrp).1
  have h3 := (hr l r h).1
  unfold exactBnd
  obtain ⟨k, hk⟩ : ∃ k, N + 1 - rk l = k + 1 := ⟨N - rk l, by omega⟩
  rw [hk]
  simp only [exactBndF, h, h0, if_false, hrp]
  rw [exactBndF_stable ns rk N hr hp k (N + 1 - rk r.nv.parent') _ (by omega) (Nat.le_refl _)]

/-- A balanced, clean, ranked bucket with the keys of rebalance has exact keys. -/
theorem bktKeys_of_rbl (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : rblKeysB W B bnd none) (hr : bktRanked B) : ∃ bnd', bktKeysB W B bnd' := by
  obtain ⟨rk, N, hrk⟩ := hr
  have hcl := hc.2.2.2.2.2.2.2.1
  -- the parent of a node: a branch of the bucket, its entries' children distinct
  have hpar : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null →
      ∃ rp, B.ns !! r.nv.parent' = some rp ∧ (rp.ws.map WEntry.pgid).Nodup := by
    intro l r h h0
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := hcl l r h
    obtain ⟨rp, hrp, hbr, -⟩ := h14 h0
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := hcl _ rp hrp
    exact ⟨rp, hrp, (h12 hbr).2.1⟩
  have hp : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → (B.ns !! r.nv.parent').isSome := by
    intro l r h h0
    obtain ⟨rp, hrp, -⟩ := hpar l r h h0
    rw [hrp]; rfl
  let bnd' := exactBnd B.ns rk N
  -- the parent clause, with the exact bounds
  have hidx : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → ∃ rp i w,
      B.ns !! r.nv.parent' = some rp ∧ rp.ws[i]? = some w ∧ w.pgid = r.nv.pgid' ∧ w.key = r.key ∧
      bndIn (bnd l) (entryBnd (bnd r.nv.parent') rp.ws i) ∧
      bnd' l = entryBnd (bnd' r.nv.parent') rp.ws i := by
    intro l r h h0
    obtain ⟨-, h2, -⟩ := hk.2.2 l r h
    obtain ⟨-, rp, i, w, hrp, hw, hg, hkey, hin⟩ := h2 h0
    refine ⟨rp, i, w, hrp, hw, hg, hkey, hin, ?_⟩
    obtain ⟨rp', hrp', hnd⟩ := hpar l r h h0
    rw [hrp] at hrp'; cases hrp'
    show exactBnd B.ns rk N l = entryBnd (exactBnd B.ns rk N r.nv.parent') rp.ws i
    rw [exactBnd_child B.ns rk N hrk hp l r rp h h0 hrp, pickIdx_eq rp.ws _ hnd i w hw hg]
  -- the bounds are inside the exact ones
  have hin : ∀ d l r, N - rk l ≤ d → B.ns !! l = some r → bndIn (bnd l) (bnd' l) := by
    intro d
    induction d with
    | zero =>
      intro l r hd h
      by_cases h0 : r.nv.parent' = null
      · show bndIn (bnd l) (exactBnd B.ns rk N l)
        rw [exactBnd_root B.ns rk N l r (hrk l r h).1 h h0]; exact bndIn_none _
      · obtain ⟨rp, -, -, hrp, -⟩ := hidx l r h h0
        have h1 := (hrk l r h).2 h0
        have h2 := (hrk _ rp hrp).1
        omega
    | succ d ih =>
      intro l r hd h
      by_cases h0 : r.nv.parent' = null
      · show bndIn (bnd l) (exactBnd B.ns rk N l)
        rw [exactBnd_root B.ns rk N l r (hrk l r h).1 h h0]; exact bndIn_none _
      · obtain ⟨rp, i, w, hrp, hw, hg, -, hin, he⟩ := hidx l r h h0
        have h1 := (hrk l r h).2 h0
        have h2 := (hrk _ rp hrp).1
        have ihp := ih _ rp (by omega) hrp
        rw [he]
        exact bndIn_transX _ _ _ hin
          (bndIn_childX (bnd r.nv.parent') (bnd' r.nv.parent') (wKey rp.ws) rp.ws.length i ihp)
  have hin' : ∀ l r, B.ns !! l = some r → bndIn (bnd l) (bnd' l) :=
    fun l r h => hin _ l r (Nat.le_refl _) h
  refine ⟨bnd', hk.1, hk.2.1, fun l r h => ?_⟩
  obtain ⟨k1, -, k3, k4, k5⟩ := hk.2.2 l r h
  refine ⟨fun w hw => keyIn_bndInX _ _ _ (k1 w hw) (hin' l r h), fun h0 => ?_, fun h0 => ?_,
    fun hb => ?_, fun hl hu hp' => k4 (by simp) hl hu hp', fun hl w hw hf hr0 => (k5 hl w hw).2 hf hr0⟩
  · exact exactBnd_root B.ns rk N l r (hrk l r h).1 h h0
  · obtain ⟨rp, i, w, hrp, hw, hg, hkey, -, he⟩ := hidx l r h h0
    obtain ⟨hkn, -⟩ := (hk.2.2 l r h).2.1 h0
    exact ⟨hkn, rp, i, w, hrp, hw, hg, hkey, he⟩
  · obtain ⟨h2, -, kind, hkind⟩ := k3 hb
    refine ⟨h2 (by simp), kind, fun i w hw => ⟨(hkind i w hw).1, fun hnm => ?_⟩⟩
    obtain ⟨pg, hpg, hc0, hfl, hpk, htk⟩ := (hkind i w hw).2 hnm
    refine ⟨pg, hpg, hc0, hfl, hpk, ?_⟩
    exact treeKeys_bndIn _ _ _ _ _ _ htk
      (bndIn_childX (bnd l) (bnd' l) (wKey r.ws) r.ws.length i (hin' l r h))

end pure

end bbolt
end EtcdGrove
end Perennial
