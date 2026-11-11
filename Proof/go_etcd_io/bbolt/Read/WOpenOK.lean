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
public import Proof.go_etcd_io.bbolt.Write.BoundNest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

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

theorem pageW_leaf' (pg : List w8) (i : Nat) (h : pageFlags pg = leafPageFlag) :
    pageW pg i = ⟨W32 (leafFlags pg i : Int), W64 0, leafKey pg i, leafValue pg i, Src.view, Src.view⟩ := by
  unfold pageW; rw [if_pos h]

theorem leafFlags_lt (pg : List w8) (i : Nat) : leafFlags pg i < 2 ^ 32 := by
  unfold leafFlags; exact BitVec.isLt _

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
      refine Or.inr (Or.inr ⟨hroot, ht, fun d hd => hc.2.2.2.2.2.2.2.2.2.1 l i w.pgid hpos d hd,
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

/-- **A nested bucket's entry at a leaf of a searchable bucket**: its value well-formed, its
source the view's or persistent, `entryIn`, its tree's keys (a stored bucket), and the bucket not
an inline one without a root node (whose page holds no nested bucket). -/
theorem leafBkt (p : w64) (hI : posI X B p) (ws : List WEntry)
    (hL : ltree X bl p = some (true, ws)) (w : WEntry) (hw : w ∈ ws) (hf : isBktFlag w.flags)
    (hbm : B.bm !! w.key = none) :
    bvalOK X.v.pages X.t.mv.pgid'.toNat w.value ∧ (w.vs = Src.view ∨ w.vs = Src.own DFrac.discard) ∧
      entryIn X.v B w.key w.value ∧
      (inBucketRoot w.value ≠ 0 → treeKeys X.v.pages (inBucketRoot w.value) none none) ∧
      ¬ (B.ib.root' = W64 0 ∧ B.bv.rootNode' = null) := by
  have hc := bktC X bl B hB hb
  obtain ⟨bnd, hbk⟩ := bktK X bl B hB hb
  have hv := viewW X bl B hB hb
  rcases hI with ⟨l, rn, hres, hrn⟩ | ⟨h0, hrn, rfl⟩ | ⟨hi, ht, hnm, ⟨c, hpr, hown⟩, lo, hi', htk⟩
  · rw [ltree_node X bl B p l rn hB hres hrn] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    have hnc := hc.2.2.2.2.2.2.2.1 l rn hrn
    obtain ⟨hbv, hvs⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.1 hlf w hw hf
    refine ⟨hbv (by simp [hbm]), hvs, Or.inl ⟨l, rn, w, hrn, hlf, hw, rfl, hf, rfl⟩, ?_, ?_⟩
    · intro hroot
      exact (hbk.2.2 l rn hrn).2.2.2.2.2 hlf w hw hf hroot (by simp [opened, hbm])
    · rintro ⟨-, hrn0⟩
      rw [(hc.2.2.1 hrn0).1] at hrn; simp at hrn
  · exfalso
    have hres : resolve B (W64 0) = none := by simp [resolve, h0, hrn]
    have hwp : wpageAt X.v B (W64 0) = some (B.bv.page', B.ipg) := by simp [wpageAt, h0]
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    have hg := (hc.1 h0 hrn).2.2.1
    unfold pageWs at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi
    rw [pageW_leaf' _ _ hg.2.1] at hf
    have := isBktFlag_mod _ hf
    have := (hg.2.2.2.2 i hi).2
    omega
  · have hres : resolve B p = none := by
      rw [resolve_tree B p hi]
      have := hnm p.toNat (by obtain ⟨pg, hpg, -⟩ := treeWF_page ht; exact treeHas.root _ pg hpg)
      rwa [LR.w64_toNat_eq] at this
    obtain ⟨-, pg, hpg, hwp, hpt, -⟩ := posOK_tree_page X B p hi ht hnm
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    unfold pageWs at hw
    obtain ⟨i, hic, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hic
    rw [pageW_leaf' _ _ hlf] at hf hbm ⊢
    have hmod := isBktFlag_mod _ hf
    have hmod' : leafFlags pg i % 2 = bucketLeafFlag := by unfold bucketLeafFlag; exact hmod
    simp only
    have hbw : bucketWF X.v.pages X.t.mv.pgid'.toNat (leafValue pg i) := by
      cases hpt with
      | leaf _ _ _ _ hbk' => exact hbk' i hic hmod'
      | branch _ _ hf' _ _ => rw [hlf] at hf'; exact absurd hf' (by unfold leafPageFlag branchPageFlag; decide)
    obtain ⟨C, hok, hvC⟩ := hv
    have hpv : X.v.pages = C.pages := by rw [← hvC]; rfl
    have hgood : pageGood pg := hok.1.2.1.1 _ pg (by rw [← hpv]; exact hpg)
    -- the nested-plainness clause, from the view page (`viewWF_matNest`)
    refine ⟨⟨hbw, fun h0 => ⟨(hgood.1 hlf i hic).2 hmod' h0,
      Write.viewWF_leafInl X.v ⟨C, hok, hvC⟩ _ pg hpg hlf i hic hmod' h0⟩,
      fun _ bpg hbp => viewWF_matNest X.v ⟨C, hok, hvC⟩ _ pg hpg hlf i hic hmod' bpg hbp⟩,
      Or.inl trivial, Or.inr ⟨c, p.toNat, pg, i, hpr, hown, hpg, hlf, hic, rfl, hmod', rfl⟩, ?_,
      fun h => hi h.1⟩
    intro hroot
    cases htk with
    | leaf _ pg' _ _ hpg' _ _ hnest =>
      rw [hpg] at hpg'; cases hpg'; exact hnest i hic hmod' hroot
    | branch _ pg' _ _ _ hpg' hf' =>
      rw [hpg] at hpg'; cases hpg'; rw [hlf] at hf'
      exact absurd hf' (by unfold leafPageFlag branchPageFlag; decide)

/-- **Every position of a logical stack of a searchable bucket is a `posI`.** -/
theorem lPath_posI (els : List elemRef) (pids : List w64) (hp : lPath X bl els pids) :
    ∀ (j : Nat) (p : w64), pids[j]? = some p → posI X B p := by
  obtain ⟨-, hlen, hhd, hstep⟩ := hp
  intro j
  induction j with
  | zero =>
    intro p hp0
    have : X.rootPid bl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
    rw [List.head?_eq_getElem?, this] at hhd
    rw [hhd] at hp0; cases hp0
    exact posI_root X bl B hB hb
  | succ j ih =>
    intro p hp1
    have hj1 : j + 1 < pids.length := (List.getElem?_eq_some_iff.1 hp1).1
    have hje : j < els.length := by omega
    obtain ⟨-, lf, ws, hL, hnext, -⟩ := hstep j els[j] pids[j]
      (List.getElem?_eq_getElem hje) (List.getElem?_eq_getElem (by omega))
    obtain ⟨rfl, w, hw, hpn⟩ := hnext (by omega)
    rw [hp1] at hpn; cases hpn
    exact posI_step X bl B hB hb _ (ih _ (List.getElem?_eq_getElem (by omega))) ws hL _ w hw

/-- Every entry of a leaf of a searchable bucket is live. -/
theorem leaf_live (p : w64) (hI : posI X B p) (ws : List WEntry)
    (hL : ltree X bl p = some (true, ws)) (w : WEntry) (hw : w ∈ ws) :
    w.ks ≠ Src.stale ∧ w.vs ≠ Src.stale := by
  have hc := bktC X bl B hB hb
  rcases hI with ⟨l, rn, hres, hrn⟩ | ⟨h0, hrn, rfl⟩ | ⟨hi, ht, hnm, -, -⟩
  · rw [ltree_node X bl B p l rn hB hres hrn] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    exact (hc.2.2.2.2.2.2.2.1 l rn hrn).2.2.2.2.2.1 w hw
  · have hres : resolve B (W64 0) = none := by simp [resolve, h0, hrn]
    have hwp : wpageAt X.v B (W64 0) = some (B.bv.page', B.ipg) := by simp [wpageAt, h0]
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    unfold pageWs at hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
    unfold pageW; split <;> simp
  · have hres : resolve B p = none := by
      rw [resolve_tree B p hi]
      have := hnm p.toNat (by obtain ⟨pg, hpg, -⟩ := treeWF_page ht; exact treeHas.root _ pg hpg)
      rwa [LR.w64_toNat_eq] at this
    obtain ⟨-, pg, hpg, hwp, -⟩ := posOK_tree_page X B p hi ht hnm
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    unfold pageWs at hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
    unfold pageW; split <;> simp

/-- A live source stays live as `seek` returns it (`leafSrc`). -/
theorem leafSrc_live (s : Src) (hs : s ≠ Src.stale) : leafSrc X bl s ≠ Src.stale := by
  have hc := bktC X bl B hB hb
  unfold leafSrc; rw [hB]; simp only
  split
  · rename_i h
    rcases (hc.1 h.1 h.2).2.1 with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> intro h' <;> cases h'
  · exact hs

/-- The leaf at the end of a logical stack. -/
theorem lPath_leaf (els : List elemRef) (pids : List w64) (hp : lPath X bl els pids) :
    ∃ (p : w64) (ws : List WEntry), (∃ j : Nat, pids[j]? = some p) ∧ ltree X bl p = some (true, ws) ∧ lLeaf X bl pids = ws := by
  obtain ⟨hne, hlen, -, hstep⟩ := hp
  have hpos : 0 < pids.length := by
    rw [hlen]; cases els with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hj : pids.length - 1 < els.length := by omega
  obtain ⟨-, lf, ws, hL, -, hlast⟩ := hstep (pids.length - 1) els[pids.length - 1]
    pids[pids.length - 1] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
  have hlf := hlast (by omega)
  subst hlf
  refine ⟨_, ws, ⟨_, List.getElem?_eq_getElem (by omega)⟩, hL, ?_⟩
  unfold lLeaf
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  simp only [hL]

/-- **A stored nested bucket's leaves hold no nested bucket** (`leafBkt`'s `bvalOK`, its third
clause: a view page's entry by `viewWF_matNest`, a node's by `nodeClean`). An opened bucket's
entry (`B.bm !! w.key ≠ none`) is excluded: `nodeClean` constrains its value only while it is
not opened. -/
theorem leafBkt_nest_plain (p : w64) (hI : posI X B p) (ws : List WEntry)
    (hL : ltree X bl p = some (true, ws)) (w : WEntry) (hw : w ∈ ws) (hf : isBktFlag w.flags)
    (hbm : B.bm !! w.key = none)
    (h0 : inBucketRoot w.value ≠ 0) (pg : List w8) (hpg : bktLeafPg X.v.pages w.value pg) :
    ∀ j < pageCount pg, leafFlags pg j % 2 = 0 := fun j hj =>
  ((leafBkt X bl B hB hb p hI ws hL w hw hf hbm).1.2.2 h0 pg hpg j hj).1

end posi

section found
variable [GooseExts]

omit [GooseExts] in
theorem wsAt_of_mem : ∀ (ws : List WEntry), Write.wsPw ws → ∀ w ∈ ws, ws[wsIdx ws w.key]? = some w
  | [], _, w, hw => by cases hw
  | a :: t, hs, w, hw => by
    rw [Write.wsPw, List.pairwise_cons] at hs
    rcases List.mem_cons.1 hw with rfl | hw'
    · unfold wsIdx
      rw [List.takeWhile_cons_of_neg (by simpa using go.goStringLt_irrefl w.key)]
      rfl
    · have ih := wsAt_of_mem t hs.2 w hw'
      have hlt := hs.1 w hw'
      unfold wsIdx at ih ⊢
      rw [List.takeWhile_cons_of_pos (by simpa using hlt), List.length_cons]
      simpa using ih

open Write LR in
/-- **The entry a route lands on is the bucket's only entry of that key.** -/
theorem route_found_at (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64) (k : List w8)
    (hb : bktLocalOK X bl) (hp : lPath X bl els pids) (hr : lRoutes X bl els pids k)
    (w : WEntry) (hw : w ∈ X.allEnts bl) (hk : w.key = k) :
    (lLeaf X bl pids)[wsIdx (lLeaf X bl pids) k]? = some w := by
  obtain ⟨-, B, hB, hc, ⟨bnd, hbk⟩, -, -, hv⟩ := hb
  have hR := LR.lRoute_of X bl els pids k hp hr
  obtain ⟨last, b', ws, hgl, hL, hmem, hI, hk'⟩ :=
    LR.route_main X bl B bnd _ hB hc hbk hv k pids hR hp.2.2.1
  have hleaf : lLeaf X bl pids = ws := by unfold lLeaf; rw [hgl]; simp only [hL]
  rw [hleaf]
  have hs := (LR.bInvL_leaf X bl B bnd _ hB hc hbk hv last b' hI ws hL).1
  have hwalk := LR.bInvL_walk X bl B bnd _ hB hc hbk hv X.fuel _ _
    (LR.bInvL_root X bl B bnd _ hB hc hbk hv)
  have hall : X.allEnts bl =
      ((lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none)).map fun x => x.2.2).flatten := by
    unfold WX.allEnts WX.leaves; rw [lleavesB_snd]
  subst hk
  rw [hall, List.mem_flatten] at hw
  obtain ⟨l, hl, hwl⟩ := hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  have hkx := hwalk.1 x hx w hwl
  have hxy : x = (last, b', ws) := by
    apply Classical.byContradiction
    intro hne
    have := pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hwalk.2.1 x hx _ hmem hne
    exact this w.key hkx hk'
  subst hxy
  exact wsAt_of_mem ws hs w hwl

end found

end WOpen

end bbolt
end EtcdGrove
end Perennial
