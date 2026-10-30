/-
A bucket whose node records changed only in what the invariants do not read (`nrecEq`: the
unbalanced flag, the slices' addresses): it stays clean, keeps its keys (`rblKeysB_sim`), its
nested buckets' entries (`entryIn_sim`) and its tokens (`bktToks_set`).
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The record `r'` is `r` but for its unbalanced flag and its slices. -/
def nrecEq (r r' : NRec) : Prop :=
  r'.ws = r.ws ∧ r'.cs = r.cs ∧ r'.ins.length = r.ins.length ∧ r'.key = r.key ∧
  r'.ksrc = r.ksrc ∧ r'.nv.bucket' = r.nv.bucket' ∧ r'.nv.isLeaf' = r.nv.isLeaf' ∧
  r'.nv.spilled' = r.nv.spilled' ∧ r'.nv.key' = r.nv.key' ∧ r'.nv.pgid' = r.nv.pgid' ∧
  r'.nv.parent' = r.nv.parent'

theorem nrecEq_refl (r : NRec) : nrecEq r r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `B'` is `B` with node records related by `nrecEq`. -/
def bktSim (B B' : BRec) : Prop :=
  B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧ B'.ipg = B.ipg ∧ B'.isrc = B.isrc ∧
  (∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧ nrecEq ry ry') ∧
  (∀ y ry', B'.ns !! y = some ry' → ∃ ry, B.ns !! y = some ry ∧ nrecEq ry ry')

theorem rf_lookup (ns : GMap Loc NRec) (l : Loc) (r' : NRec) (y : Loc) :
    (<[l := r']> ns) !! y = if y = l then some r' else ns !! y := by
  by_cases h : y = l
  · subst h; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]

theorem bktSim_set (B : BRec) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (he : nrecEq r r') : bktSim B { B with ns := <[l := r']> B.ns } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun y ry hy => ?_, fun y ry' hy => ?_⟩
  · show ∃ ry', (<[l := r']> B.ns) !! y = some ry' ∧ _
    rw [rf_lookup]
    by_cases h : y = l
    · subst h; rw [hr] at hy; cases hy; exact ⟨r', by rw [if_pos rfl], he⟩
    · exact ⟨ry, by rw [if_neg h]; exact hy, nrecEq_refl ry⟩
  · change (<[l := r']> B.ns) !! y = some ry' at hy
    rw [rf_lookup] at hy
    by_cases h : y = l
    · subst h; rw [if_pos rfl] at hy; cases hy; exact ⟨r, hr, he⟩
    · rw [if_neg h] at hy; exact ⟨ry', hy, nrecEq_refl ry'⟩

theorem bktSim_trans {B1 B2 B3 : BRec} (h1 : bktSim B1 B2) (h2 : bktSim B2 B3) : bktSim B1 B3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1'⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, h2'⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1,
    fun y ry hy => ?_, fun y ry' hy => ?_⟩
  · obtain ⟨r2, hr2, e⟩ := g1 y ry hy
    obtain ⟨r3, hr3, e'⟩ := g2 y r2 hr2
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := e
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := e'
    exact ⟨r3, hr3, p1.trans q1, p2.trans q2, p3.trans q3, p4.trans q4, p5.trans q5, p6.trans q6,
      p7.trans q7, p8.trans q8, p9.trans q9, p10.trans q10, p11.trans q11⟩
  · obtain ⟨r2, hr2, e'⟩ := h2' y ry' hy
    obtain ⟨r1, hr1, e⟩ := h1' y r2 hr2
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := e
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := e'
    exact ⟨r1, hr1, p1.trans q1, p2.trans q2, p3.trans q3, p4.trans q4, p5.trans q5, p6.trans q6,
      p7.trans q7, p8.trans q8, p9.trans q9, p10.trans q10, p11.trans q11⟩

theorem pagePosAt_sim {B B' : BRec} (h : bktSim B B') (l : Loc) (i : Nat) (c : w64) :
    pagePosAt B' l i c ↔ pagePosAt B l i c := by
  obtain ⟨-, -, hnm, -, -, -, hf, hb⟩ := h
  constructor
  · rintro ⟨r', w, hr', hbr, hw, hc, hn⟩
    obtain ⟨r, hr, e⟩ := hb l r' hr'
    exact ⟨r, w, hr, by rw [← e.2.2.2.2.2.2.1]; exact hbr, by rw [← e.1]; exact hw, hc,
      by rw [← hnm]; exact hn⟩
  · rintro ⟨r, w, hr, hbr, hw, hc, hn⟩
    obtain ⟨r', hr', e⟩ := hf l r hr
    exact ⟨r', w, hr', by rw [e.2.2.2.2.2.2.1]; exact hbr, by rw [e.1]; exact hw, hc,
      by rw [hnm]; exact hn⟩

variable (W : WView) (hwm : Nat) (bl : Loc)

theorem bktClean_sim {B B' : BRec} (h : bktSim B B') (hc : bktClean W hwm bl B) :
    bktClean W hwm bl B' := by
  have hpos := pagePosAt_sim h
  obtain ⟨hbv, hib, hnm, hbm, hipg, hisrc, hf, hb⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hib, hbv, hisrc, hipg]; exact c1
  · rw [hib, hbv]; exact c2
  · intro h0
    rw [hbv] at h0
    obtain ⟨hns, hnm0⟩ := c3 h0
    refine ⟨?_, by rw [hnm]; exact hnm0⟩
    apply GMap.ext; intro y
    cases hy : B'.ns !! y with
    | none => show none = (∅ : GMap Loc NRec) !! y; simp
    | some ry' =>
      obtain ⟨ry, hry, -⟩ := hb y ry' hy
      rw [hns] at hry; simp at hry
  · rw [hbv, hnm, hib]; exact c4
  · intro c l hl
    rw [hnm] at hl
    obtain ⟨hnn, r, hr, hp⟩ := c5 c l hl
    obtain ⟨r', hr', e⟩ := hf l r hr
    exact ⟨hnn, r', hr', by rw [e.2.2.2.2.2.2.2.2.2.1]; exact hp⟩
  · rw [hib, hbv]; exact c6
  · intro h0 l r' hr'
    rw [hib] at h0
    obtain ⟨r, hr, e⟩ := hb l r' hr'
    rw [e.2.2.2.2.2.2.1]; exact c7 h0 l r hr
  · intro l r' hr'
    obtain ⟨r, hr, e⟩ := hb l r' hr'
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := e
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := c8 l r hr
    refine ⟨by rw [q6]; exact n1, by rw [q3, q1]; exact n2, by rw [q1]; exact n3,
      by rw [q1]; exact n4, by rw [q1]; exact n5, by rw [q8]; exact n6,
      by rw [hnm, q10]; exact n7, by rw [hib, q10]; exact n8, by rw [hib, q10]; exact n9,
      by rw [q9, q4, q5]; exact n10, by rw [q7, q1, hbm]; exact n11, ?_, by rw [q11, hbv]; exact n13,
      ?_, by rw [q2]; exact n15, ?_⟩
    · intro hl
      rw [q7] at hl
      obtain ⟨a1, a2, a3⟩ := n12 hl
      rw [q1]
      refine ⟨a1, a2, fun w hw => ⟨(a3 w hw).1, fun l' hl' => ?_, by rw [hnm]; exact (a3 w hw).2.2⟩⟩
      rw [hnm] at hl'
      obtain ⟨r0, hr0, hp0⟩ := (a3 w hw).2.1 l' hl'
      obtain ⟨r0', hr0', e0⟩ := hf l' r0 hr0
      exact ⟨r0', hr0', by rw [e0.2.2.2.2.2.2.2.2.2.2]; exact hp0⟩
    · intro hp
      rw [q11] at hp ⊢
      obtain ⟨rp, hrp, hrl, hin, w, hw, hwp⟩ := n14 hp
      obtain ⟨rp', hrp', ep⟩ := hf _ rp hrp
      exact ⟨rp', hrp', by rw [ep.2.2.2.2.2.2.1]; exact hrl, by rw [ep.2.1]; exact hin, w,
        by rw [ep.1]; exact hw, by rw [q10]; exact hwp⟩
    · intro c hcin
      rw [q2] at hcin
      obtain ⟨rc, hrc, hpc⟩ := n16 c hcin
      obtain ⟨rc', hrc', ec⟩ := hf c rc hrc
      exact ⟨rc', hrc', by rw [ec.2.2.2.2.2.2.2.2.2.2]; exact hpc⟩
  · intro l1 i1 c1 l2 i2 c2 h1 h2 hne d hd
    rw [hpos] at h1 h2
    exact c9 l1 i1 c1 l2 i2 c2 h1 h2 hne d hd
  · intro l i c hp d hd
    rw [hpos] at hp
    rw [hnm]; exact c10 l i c hp d hd

theorem rblKeysB_sim {B B' : BRec} (h : bktSim B B') (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc dfc' : Option Loc) (hk : rblKeysB W B bnd dfc)
    (hd2 : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → dfc' ≠ some y → 2 ≤ ry.ws.length)
    (hd4 : ∀ y ry', B'.ns !! y = some ry' → dfc' ≠ some y → ry'.nv.isLeaf' = true →
      ry'.nv.unbalanced' = false → ry'.nv.parent' ≠ null → 0 < ry'.ws.length) :
    rblKeysB W B' bnd dfc' := by
  obtain ⟨hbv, hib, hnm, hbm, hipg, hisrc, hf, hb⟩ := h
  obtain ⟨k1, k2, k3⟩ := hk
  refine ⟨by rw [hbv, hib]; exact k1, fun r' hr' => ?_, fun l r' hr' => ?_⟩
  · rw [hbv] at hr'
    obtain ⟨r, hr, e⟩ := hb _ r' hr'
    rw [e.2.2.2.2.2.2.2.2.2.2]; exact k2 r hr
  obtain ⟨r, hr, e⟩ := hb l r' hr'
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := e
  obtain ⟨n1, n2, n3, n4, n5⟩ := k3 l r hr
  refine ⟨by rw [q1]; exact n1, fun hp => ?_, fun hl => ?_, hd4 l r' hr', fun hl => ?_⟩
  · rw [q11] at hp ⊢
    obtain ⟨hkey, rp, i, w, hrp, hw, hwp, hwk, hbn⟩ := n2 hp
    obtain ⟨rp', hrp', ep⟩ := hf _ rp hrp
    exact ⟨by rw [q9]; exact hkey, rp', i, w, hrp', by rw [ep.1]; exact hw, by rw [q10]; exact hwp,
      by rw [q4]; exact hwk, by rw [ep.1]; exact hbn⟩
  · rw [q7] at hl
    obtain ⟨-, a2, kind, a3⟩ := n3 hl
    refine ⟨fun hd => by rw [q1]; exact hd2 l r hr hl hd, by rw [q1]; exact a2, kind, ?_⟩
    intro i w hw
    rw [q1] at hw
    obtain ⟨b1, b2⟩ := a3 i w hw
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rw [hnm] at hl'
      obtain ⟨r0, hr0, hk0⟩ := b1 l' hl'
      obtain ⟨r0', hr0', e0⟩ := hf l' r0 hr0
      exact ⟨r0', hr0', by rw [e0.2.2.2.2.2.2.1]; exact hk0⟩
    · rw [hnm] at hn
      rw [q1]; exact b2 hn
  · rw [q7] at hl; rw [q1]
    have hop : opened B' = opened B := by unfold opened; rw [hbm]
    rw [hop]; exact n5 hl

theorem rblAcyc_sim {B B' : BRec} (h : bktSim B B') (ha : rblAcyc B) : rblAcyc B' := by
  obtain ⟨ht, hh⟩ := ha
  refine ⟨ht, fun l r' hr' hp => ?_⟩
  obtain ⟨r, hr, e⟩ := h.2.2.2.2.2.2.2 l r' hr'
  rw [e.2.2.2.2.2.2.2.2.2.2] at hp ⊢
  exact hh l r hr hp

theorem rblHt_sim {B B' : BRec} (h : bktSim B B') (ha : rblHt W B) : rblHt W B' := by
  obtain ⟨ht, pht, hp, hh⟩ := ha
  refine ⟨ht, pht, hp, fun l r' hr' => ?_⟩
  obtain ⟨r, hr, e⟩ := h.2.2.2.2.2.2.2 l r' hr'
  obtain ⟨h1, h2⟩ := hh l r hr
  rw [e.2.2.2.2.2.2.1, e.1, h.2.2.1]
  exact ⟨h1, h2⟩

theorem entryIn_sim {B B' : BRec} (h : bktSim B B') (k v : List w8) (he : entryIn W B k v) :
    entryIn W B' k v := by
  have hpos := pagePosAt_sim h
  obtain ⟨hbv, hib, hnm, hbm, hipg, hisrc, hf, hb⟩ := h
  rcases he with ⟨l, r, w, hr, hl, hw, hk, hbk, hv⟩ | ⟨c, p, pg, i, hc, ho, hpg, hlf, hi, hk, hfl, hv⟩
  · obtain ⟨r', hr', e⟩ := hf l r hr
    exact Or.inl ⟨l, r', w, hr', by rw [e.2.2.2.2.2.2.1]; exact hl, by rw [e.1]; exact hw, hk, hbk, hv⟩
  · refine Or.inr ⟨c, p, pg, i, ?_, ho, hpg, hlf, hi, hk, hfl, hv⟩
    unfold posRoot at hc ⊢
    rw [hbv, hib]
    rcases hc with h1 | ⟨l, j, hp, hlt⟩
    · exact Or.inl h1
    · exact Or.inr ⟨l, j, (hpos l j _).2 hp, hlt⟩

end pure

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

theorem nodeToks_eq (γ : GName) (W : WView) (B B' : BRec) (r r' : NRec) (hbm : B'.bm = B.bm)
    (hnm : B'.nm = B.nm) (hp : r'.nv.pgid' = r.nv.pgid') (hws : r'.ws = r.ws)
    (hl : r'.nv.isLeaf' = r.nv.isLeaf') : nodeToks (GF := GF) γ W B' r' = nodeToks γ W B r := by
  have hop : opened B' = opened B := by unfold opened; rw [hbm]
  unfold nodeToks
  rw [hp, hws, hl, hop, hnm]

theorem bktToks_set (γ : GName) (W : WView) (B : BRec) (l : Loc) (r r' : NRec)
    (hr : B.ns !! l = some r) (he : nrecEq r r') :
    bktToks (GF := GF) γ W { B with ns := <[l := r']> B.ns } ⊣⊢ bktToks γ W B := by
  unfold bktToks
  simp only
  split
  · exact .rfl
  · have e1 : ∀ x, nodeToks (GF := GF) γ W { B with ns := <[l := r']> B.ns } x = nodeToks γ W B x :=
      fun x => nodeToks_eq γ W B _ x x rfl rfl rfl rfl rfl
    simp only [e1]
    have e2 : nodeToks (GF := GF) γ W B r' = nodeToks γ W B r :=
      nodeToks_eq γ W B B r r' rfl rfl he.2.2.2.2.2.2.2.2.2.1 he.1 he.2.2.2.2.2.2.1
    constructor
    · iintro H
      icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
        (show Std.get? (<[l := r']> B.ns) l = some r' by show (<[l := r']> B.ns) !! l = _; rw [GMap.lookup_insert])) $$ H
        with ⟨Hr, Hback⟩
      ihave H := Hback $$ %r [Hr]
      · rw [e2]; iexact Hr
      rw [show Std.insert (<[l := r']> B.ns) l r = B.ns by
        show <[l := r]> (<[l := r']> B.ns) = B.ns
        rw [GMap.insert_insert, GMap.insert_id _ _ _ hr]]
      iexact H
    · iintro H
      icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
        (show Std.get? B.ns l = some r from hr)) $$ H with ⟨Hr, Hback⟩
      ihave H := Hback $$ %r' [Hr]
      · rw [e2]; iexact Hr
      iexact H

end toks

end bbolt
end EtcdGrove
end Perennial
