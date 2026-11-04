/-
The writer's opened buckets, pure (U6e, `notes/bbolt-proof-plan.md`): the positions of a logical
stack of a searchable bucket (`posI`: a node, the inline page, or a view page of a page position's
subtree, with its keys), and what a nested bucket's entry at a leaf gives (`leafBkt`: its value
well-formed, its source, `entryIn`, its tree's keys); the entry a route lands on is the bucket's
only entry of that key (`route_found_at`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.LRoutes
public import Proof.go_etcd_io.bbolt.Read.WPos
public import Proof.go_etcd_io.bbolt.Write.Bound

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WOpen

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section posi
variable [GooseExts]

/-- **A position of a searchable bucket** `B`: a materialized node, the inline page (no root
node), or a view page of a page position's subtree (well-formed, nothing below it materialized,
with keys). -/
def posI (X : WX) (B : BRec) (p : w64) : Prop :=
  (∃ l rn, resolve B p = some l ∧ B.ns !! l = some rn) ∨
  (B.ib.root' = W64 0 ∧ B.bv.rootNode' = null ∧ p = W64 0) ∨
  (B.ib.root' ≠ W64 0 ∧ treeWF X.v.pages X.t.mv.pgid'.toNat p.toNat ∧
    (∀ d, treeHas X.v.pages p.toNat d → B.nm !! W64 (d : Int) = none) ∧
    (∃ c, posRoot B c ∧ ownHas X.v.pages c p.toNat) ∧ ∃ lo hi, treeKeys X.v.pages p.toNat lo hi)

theorem ownHas_snoc (P : Pages) {c p : Nat} (h : ownHas P c p) (pg : List w8) (hpg : P !! p = some pg)
    (hf : pageFlags pg = branchPageFlag) (i : Nat) (hi : i < pageCount pg) (pgc : List w8)
    (hc : P !! branchPgid pg i = some pgc) : ownHas P c (branchPgid pg i) := by
  induction h with
  | root r pg0 h0 =>
    rw [h0] at hpg; cases hpg
    exact ownHas.child r pg i _ h0 hf hi (ownHas.root _ pgc hc)
  | child r pg0 j id h0 hf0 hj _ ih =>
    exact ownHas.child r pg0 j _ h0 hf0 hj (ih hpg)

theorem treeWF_page {P : Pages} {hwm p : Nat} (h : treeWF P hwm p) :
    ∃ pg, P !! p = some pg ∧ pageTreeWF P hwm pg pg.length := by
  cases h with
  | page _ pg _ _ hpg _ _ hpt => exact ⟨pg, hpg, hpt⟩

theorem isBktFlag_mod (f : Nat) (h : isBktFlag (W32 (f : Int))) : f % 2 = 1 := by
  unfold isBktFlag at h
  apply Classical.byContradiction
  intro hne
  apply h
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  omega

variable (X : WX) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B) (hb : bktLocalOK X bl)
include hB hb

theorem bktC : bktClean X.v X.t.mv.pgid'.toNat bl B := by
  obtain ⟨-, B', hB', hc, -⟩ := hb
  rw [hB] at hB'; cases hB'; exact hc

theorem bktK : bktKeys X.v B := by
  obtain ⟨-, B', hB', -, hk, -⟩ := hb
  rw [hB] at hB'; cases hB'; exact hk

theorem viewW : viewWF X.v := hb.2.choose_spec.2.2.2.2.2

/-- **The root of a searchable bucket.** -/
theorem posI_root : posI X B B.ib.root' := by
  have hc := bktC X bl B hB hb
  obtain ⟨bnd, hbk⟩ := bktK X bl B hB hb
  by_cases hrn : B.bv.rootNode' = null
  · have hns := (hc.2.2.1 hrn)
    by_cases hi : B.ib.root' = W64 0
    · exact Or.inr (Or.inl ⟨hi, hrn, hi⟩)
    · have ht := (hc.2.1 hi).2 hrn
      obtain ⟨pg, hpg, -⟩ := treeWF_page ht
      refine Or.inr (Or.inr ⟨hi, ht, fun d _ => by rw [hns.2]; rfl,
        ⟨B.ib.root'.toNat, Or.inl ⟨hrn, hi, rfl⟩, ownHas.root _ pg hpg⟩,
        none, none, hbk.1 hrn hi⟩)
  · have hnm := hc.2.2.2.1 hrn
    obtain ⟨-, rn, hrn', -⟩ := hc.2.2.2.2.1 _ _ hnm
    refine Or.inl ⟨_, rn, ?_, hrn'⟩
    unfold resolve
    split
    · simp [hrn]
    · exact hnm

/-- **A branch's child.** -/
theorem posI_step (p : w64) (hI : posI X B p) (ws : List WEntry)
    (hL : ltree X bl p = some (false, ws)) (i : Nat) (w : WEntry) (hw : ws[i]? = some w) :
    posI X B w.pgid := by
  have hc := bktC X bl B hB hb
  obtain ⟨bnd, hbk⟩ := bktK X bl B hB hb
  rcases hI with ⟨l, rn, hres, hrn⟩ | ⟨h0, hrn, rfl⟩ | ⟨hi, ht, hnm, ⟨c, hpr, hown⟩, lo, hi', htk⟩
  · rw [ltree_node X bl B p l rn hB hres hrn] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    have hnc := hc.2.2.2.2.2.2.2.1 l rn hrn
    have hroot : B.ib.root' ≠ W64 0 := by
      intro h0
      have := hc.2.2.2.2.2.2.1 h0 l rn hrn
      rw [hlf] at this; cases this
    obtain ⟨-, -, hall⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.1 hlf
    have hwm : w ∈ rn.ws := List.mem_of_getElem? hw
    obtain ⟨-, hm, hp⟩ := hall w hwm
    cases hn : B.nm !! w.pgid with
    | some l' =>
      obtain ⟨-, r', hr', -⟩ := hc.2.2.2.2.1 _ _ hn
      exact Or.inl ⟨l', r', by rw [resolve_tree B _ hroot]; exact hn, hr'⟩
    | none =>
      have ht := hp hn
      obtain ⟨pgc, hpgc, -⟩ := treeWF_page ht
      have hpos : pagePosAt B l i w.pgid := ⟨rn, w, hrn, hlf, hw, rfl, hn⟩
      obtain ⟨-, kind, hkk⟩ := ((hbk.2.2 l rn hrn).2.2.2.1 hlf)
      obtain ⟨pgk, -, -, -, -, hkeys⟩ := (hkk i w hw).2 hn
      refine Or.inr (Or.inr ⟨hroot, ht, fun d hd => hc.2.2.2.2.2.2.2.2.2 l i w.pgid hpos d hd,
        ⟨w.pgid.toNat, Or.inr ⟨l, i, by rw [LR.w64_toNat_eq]; exact hpos, w.pgid.isLt⟩,
          ownHas.root _ pgc hpgc⟩, _, _, hkeys⟩)
  · exfalso
    have hres : resolve B (W64 0) = none := by simp [resolve, h0, hrn]
    have hwp : wpageAt X.v B (W64 0) = some (B.bv.page', B.ipg) := by simp [wpageAt, h0]
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    have hg := (hc.1 h0 hrn).2.2.1
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
    exact hL.1 hg.2.1
  · have hres : resolve B p = none := by
      rw [resolve_tree B p hi]
      have := hnm p.toNat (by obtain ⟨pg, hpg, -⟩ := treeWF_page ht; exact treeHas.root _ pg hpg)
      rwa [LR.w64_toNat_eq] at this
    obtain ⟨-, pg, hpg, hwp, hpt, -⟩ := posOK_tree_page X B p hi ht hnm
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
    obtain ⟨hnl, rfl⟩ := hL
    have hbr : pageFlags pg = branchPageFlag := by
      cases hpt with
      | leaf _ _ hf _ _ => exact absurd hf hnl
      | branch _ _ hf _ _ => exact hf
    have hic : i < pageCount pg := by
      rw [← pageWs_length]; exact (List.getElem?_eq_some_iff.1 hw).1
    rw [pageWs_get pg i hic] at hw
    cases hw
    have hpgid : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
      unfold pageW; rw [if_neg hnl]
    rw [hpgid]
    rcases posOK_page_child X bl B p pg i hi ht hnm hpg hbr hic with
      ⟨l, rn, hr, -⟩ | ⟨-, h0, -⟩ | ⟨-, ht', hnm'⟩
    · exfalso
      rw [resolve_tree B _ hi] at hr
      have hch : treeHas X.v.pages p.toNat (branchPgid pg i) := by
        obtain ⟨pgc, hpgc, -⟩ : ∃ pgc, X.v.pages !! branchPgid pg i = some pgc ∧ True := by
          cases htk with
          | leaf _ pg' _ _ hpg' hf' => rw [hpg] at hpg'; cases hpg'; exact absurd hf' hnl
          | branch _ pg' _ _ _ hpg' _ _ _ hall _ =>
            rw [hpg] at hpg'; cases hpg'
            obtain ⟨cpg, hc', -⟩ := hall i hic
            exact ⟨cpg, hc', trivial⟩
        exact treeHas.sub _ pg _ hpg (pageHas.child pg i _ hbr hic (treeHas.root _ pgc hpgc))
      have := hnm _ hch
      rw [hr] at this; cases this
    · exact absurd h0 hi
    · rw [LR.branchPgid_toNat] at ht' hnm'
      obtain ⟨pgc, hpgc, -⟩ := treeWF_page ht'
      refine Or.inr (Or.inr ⟨hi, by rw [LR.branchPgid_toNat]; exact ht',
        by rw [LR.branchPgid_toNat]; exact hnm', ⟨c, hpr, ?_⟩, ?_⟩)
      · rw [LR.branchPgid_toNat]; exact ownHas_snoc _ hown pg hpg hbr i hic pgc hpgc
      · rw [LR.branchPgid_toNat]
        cases htk with
        | leaf _ pg' _ _ hpg' hf' => rw [hpg] at hpg'; cases hpg'; exact absurd hf' hnl
        | branch _ pg' _ _ _ hpg' _ _ _ _ hall =>
          rw [hpg] at hpg'; cases hpg'
          exact ⟨_, _, hall i hic⟩

end posi

end WOpen

end bbolt
end EtcdGrove
end Perennial
