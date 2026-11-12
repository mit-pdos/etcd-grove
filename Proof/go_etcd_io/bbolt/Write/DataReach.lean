/-
U7k (`notes/bbolt-proof-plan.md`): what the walk of a well-formed writer's bucket reaches. A
materialized node is reached, with its bounds `bnd` (up its parent chain: each parent's entry
selects its page id, whose subtree is smaller, `treeMeasure_child`); a leaf is then a block of
the walk. A page below a page position is reached through the pages. So an opened top-level
bucket is a root entry (`bktNested`'s `entryIn`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DataBnd
public import Proof.go_etcd_io.bbolt.Write.Fuel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section datareach
variable [GooseExts]

/-- The walk goes from position `p` with bounds `b` to `p'` with `b'`. -/
inductive Reach (L : LTree) (bl : Loc) : w64 → Bnd → w64 → Bnd → Prop
  | refl (p : w64) (b : Bnd) : Reach L bl p b p b
  | step (p : w64) (b : Bnd) (ws : List WEntry) (i : Nat) (p' : w64) (b' : Bnd) :
      L bl p = some (false, ws) → i < ws.length →
      Reach L bl (ws.getD i default).pgid (wEntryBnd b ws i) p' b' → Reach L bl p b p' b'

theorem Reach.snoc {L : LTree} {bl : Loc} {p0 : w64} {b0 : Bnd} {p : w64} {b : Bnd}
    (h : Reach L bl p0 b0 p b) (ws : List WEntry) (i : Nat) (hL : L bl p = some (false, ws))
    (hi : i < ws.length) : Reach L bl p0 b0 (ws.getD i default).pgid (wEntryBnd b ws i) := by
  induction h with
  | refl p b => exact Reach.step p b ws i _ _ hL hi (Reach.refl _ _)
  | step p b ws' i' p' b' hL' hi' _ ih => exact Reach.step p b ws' i' _ _ hL' hi' (ih hL)

theorem Reach.trans {L : LTree} {bl : Loc} {p0 : w64} {b0 : Bnd} {p1 : w64} {b1 : Bnd}
    {p2 : w64} {b2 : Bnd} (h1 : Reach L bl p0 b0 p1 b1) (h2 : Reach L bl p1 b1 p2 b2) :
    Reach L bl p0 b0 p2 b2 := by
  induction h1 with
  | refl => exact h2
  | step p b ws i p' b' hL hi _ ih => exact Reach.step p b ws i _ _ hL hi (ih h2)

theorem Reach.mem {L : LTree} {bl : Loc} (μ : w64 → Nat)
    (hdec : ∀ pid ws, L bl pid = some (false, ws) → ∀ w ∈ ws, μ w.pgid < μ pid)
    {p0 : w64} {b0 : Bnd} {p : w64} {b : Bnd} (h : Reach L bl p0 b0 p b) (ws : List WEntry)
    (hL : L bl p = some (true, ws)) : ∀ n, μ p0 < n → (p, b, ws) ∈ lleavesB L bl n p0 b0 := by
  induction h with
  | refl p b =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [lleavesB, hL]
  | step p b ws' i p' b' hL' hi _ ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [lleavesB, hL']
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_range.2 hi, ih hL n ?_⟩
    have := hdec p ws' hL' _ (getD_mem ws' i hi)
    omega

/-! ## A well-formed writer's walk -/

/-- The measure decreases along a well-formed writer's branches (`wOK_leaves_fuel'`'s). -/
theorem ltree_branch_dec (X : WX) (bl : Loc) (hok : wOK X) :
    ∀ pid ws, ltree X bl pid = some (false, ws) → ∀ w ∈ ws,
      treeMeasure X.v.pages w.pgid < treeMeasure X.v.pages pid := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  intro pid ws hL w hw
  unfold ltree at hL
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hL; cases hL
  | some B =>
    rw [hB] at hL
    simp only at hL
    have hc := wOK_bktClean X hok bl B hB
    cases hr : resolve B pid with
    | some l =>
      rw [hr] at hL
      simp only at hL
      cases hrl : B.ns !! l with
      | none => rw [hrl] at hL; cases hL
      | some r =>
        rw [hrl] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
        obtain ⟨hleaf, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have := hc.2.2.2.2.2.2.1 hin l r hrl; rw [hleaf] at this; cases this
        · have hnm : B.nm !! pid = some l := by unfold resolve at hr; rwa [if_neg hin] at hr
          obtain ⟨-, r', hr', hpid⟩ := hc.2.2.2.2.1 pid l hnm
          rw [hrl] at hr'; cases hr'
          obtain ⟨-, pg, hpg, hbr, hlen, hws⟩ := ((hok.2.2.1 bl B hB l r hrl).2 hleaf)
          rw [hpid] at hpg
          obtain ⟨i, hi, he⟩ := List.getElem_of_mem hw
          have hwi : r.ws[i]? = some w := by rw [List.getElem?_eq_getElem hi]; exact congrArg _ he
          rw [hws i w hwi]
          exact treeMeasure_child X.v hv pid pg hpg hbr i (by rw [← hlen]; exact hi)
    | none =>
      rw [hr] at hL
      simp only at hL
      cases hp : wpageAt X.v B pid with
      | none => rw [hp] at hL; cases hL
      | some x =>
        obtain ⟨pa, pg⟩ := x
        rw [hp] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
        obtain ⟨hnl, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have hrn : B.bv.rootNode' = null := by
            unfold resolve at hr; rw [if_pos hin] at hr; split at hr
            · assumption
            · cases hr
          have := wOK_inlineLeaf X bl pid hok B pa pg hB hin hrn hp
          exact absurd this hnl
        · have hpg : X.v.pages !! pid.toNat = some pg := by
            unfold wpageAt at hp; rw [if_neg hin] at hp
            cases h : X.v.pages !! pid.toNat with
            | none => rw [h] at hp; cases hp
            | some pg' => rw [h] at hp; simp only [Option.map_some, Option.some.injEq,
                            Prod.mk.injEq] at hp; rw [hp.2]
          have hbr : pageFlags pg = branchPageFlag := by
            rcases (Read.viewWF_page X.v hv _ pg hpg).2.2.2 with h | h
            · exact h
            · exact absurd h hnl
          unfold pageWs at hw
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
          rw [List.mem_range] at hi
          have : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
            unfold pageW; simp [hnl]
          rw [this]
          exact treeMeasure_child X.v hv pid pg hpg hbr i hi

theorem rootPid_lt_fuel (X : WX) (bl : Loc) :
    treeMeasure X.v.pages (X.rootPid bl) < X.fuel := by
  have := treeMeasure_le X.v.pages (X.rootPid bl)
  unfold WX.fuel; omega

theorem Reach.mem_walk (X : WX) (bl : Loc) (hok : wOK X) {p : w64} {b : Bnd}
    (h : Reach (ltree X) bl (X.rootPid bl) (none, none) p b) (ws : List WEntry)
    (hL : ltree X bl p = some (true, ws)) :
    (p, b, ws) ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none) :=
  Reach.mem _ (ltree_branch_dec X bl hok) h ws hL _ (rootPid_lt_fuel X bl)

theorem ownHas_treeHas {P : Pages} {c p : Nat} (h : ownHas P c p) : treeHas P c p := by
  induction h with
  | root r pg hpg => exact treeHas.root r pg hpg
  | child r pg i id hpg hb hi _ ih => exact treeHas.sub r pg id hpg (pageHas.child pg i id hb hi ih)

theorem isBktFlag_leaf (pg : List w8) (i : Nat) (h : leafFlags pg i % 2 = bucketLeafFlag) :
    isBktFlag (W32 (leafFlags pg i : Int)) := by
  have hlt : leafFlags pg i < 2 ^ 32 := by unfold leafFlags; exact BitVec.isLt _
  generalize leafFlags pg i = x at h hlt
  unfold isBktFlag
  have h2 : (W32 (x : Int)).toNat = x := by
    rw [BitVec.toNat_ofInt]; simp; omega
  have hk : (W32 (x : Int) &&& W32 1).toNat = x % 2 := by
    rw [BitVec.toNat_and, h2]
    show x &&& 1 = x % 2
    rw [Nat.and_one_is_mod]
  intro he
  have := congrArg BitVec.toNat he
  rw [hk] at this; unfold bucketLeafFlag at h; simp at this; omega

variable (X : WX) (bl : Loc) (B : BRec) (bnd : Loc → Bnd)
variable (hok : wOK X) (hB : X.t.bs !! bl = some B) (hbk : bktKeysB X.v B bnd)
include hok hB hbk

theorem ltree_node (m : Loc) (rm : NRec) (hres : resolve B rm.nv.pgid' = some m)
    (hrm : B.ns !! m = some rm) : ltree X bl rm.nv.pgid' = some (rm.nv.isLeaf', rm.ws) := by
  rw [ltree_of_B X bl B bnd hok hB hbk, hres]; simp [hrm]

/-- **A materialized node is reached**, with its bounds, at its page id. -/
theorem node_reach_aux : ∀ d, ∀ m rm, B.ns !! m = some rm →
    X.v.pages.size + 1 - treeMeasure X.v.pages rm.nv.pgid' = d →
    Reach (ltree X) bl (X.rootPid bl) (none, none) rm.nv.pgid' (bnd m) ∧
      resolve B rm.nv.pgid' = some m := by
  have hc := wOK_bktClean X hok bl B hB
  have hrp : X.rootPid bl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro m rm hrm hd
  have hcl := hc.2.2.2.2.2.2.2.1 m rm hrm
  have hnk := hbk.2.2 m rm hrm
  have hres : resolve B rm.nv.pgid' = some m := by
    unfold resolve
    split
    · rename_i hin
      by_cases hrn : B.bv.rootNode' = null
      · rw [(hc.2.2.1 hrn).1] at hrm; cases hrm
      · rw [if_neg hrn]
        congr 1
        by_cases hpn : rm.nv.parent' = null
        · exact hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
        · obtain ⟨rp, hrp', hrpl, -⟩ := hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
          have := hc.2.2.2.2.2.2.1 hin _ rp hrp'; rw [hrpl] at this; cases this
    · exact hcl.2.2.2.2.2.2.2.1
  refine ⟨?_, hres⟩
  by_cases hpn : rm.nv.parent' = null
  · have hroot := hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
    have hb0 := hnk.2.1 hpn
    rw [hb0, hrp]
    have hpg : rm.nv.pgid' = B.ib.root' := by
      by_cases hin : B.ib.root' = W64 0
      · rw [hin]; exact hcl.2.2.2.2.2.2.2.2.1 hin
      · have hrn : B.bv.rootNode' ≠ null := by
          intro hrn; rw [(hc.2.2.1 hrn).1] at hrm; cases hrm
        have hnm := hc.2.2.2.1 hrn
        rw [hroot] at hnm
        obtain ⟨-, r', hr', hpid⟩ := hc.2.2.2.2.1 _ _ hnm
        rw [hrm] at hr'; cases hr'; exact hpid
    rw [hpg]; exact Reach.refl _ _
  · obtain ⟨-, rp, i, w, hrp', hw, hwp, -, hbnd⟩ := hnk.2.2.1 hpn
    obtain ⟨rp2, hrp2, hrpl, -⟩ := hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
    rw [hrp'] at hrp2; cases hrp2
    -- the parent's page is a branch page whose child `i` is the node's page
    obtain ⟨-, pg, hpg, hbr, hlen, hws⟩ := (hok.2.2.1 bl B hB _ rp hrp').2 hrpl
    have hi : i < rp.ws.length := (List.getElem?_eq_some_iff.1 hw).1
    have hlt : treeMeasure X.v.pages rm.nv.pgid' < treeMeasure X.v.pages rp.nv.pgid' := by
      rw [← hwp, hws i w hw]
      exact treeMeasure_child X.v hok.2.2.2.2.2.2.2 _ pg hpg hbr i (by rw [← hlen]; exact hi)
    have hle := treeMeasure_le X.v.pages rp.nv.pgid'
    obtain ⟨hreach, hpres⟩ := ih _ (by omega) _ rp hrp' rfl
    have hL := ltree_node X bl B bnd hok hB hbk _ rp hpres hrp'
    rw [hrpl] at hL
    have := hreach.snoc rp.ws i hL hi
    have hgw : rp.ws.getD i default = w := by
      rw [List.getD_eq_getElem?_getD, hw]; rfl
    rw [hgw, hwp, ← hbnd] at this
    exact this

theorem node_reach (m : Loc) (rm : NRec) (hrm : B.ns !! m = some rm) :
    Reach (ltree X) bl (X.rootPid bl) (none, none) rm.nv.pgid' (bnd m) ∧
      resolve B rm.nv.pgid' = some m :=
  node_reach_aux X bl B bnd hok hB hbk _ m rm hrm rfl

/-- **A materialized leaf is a block of the walk.** -/
theorem leaf_block (m : Loc) (rm : NRec) (hrm : B.ns !! m = some rm)
    (hleaf : rm.nv.isLeaf' = true) :
    (rm.nv.pgid', bnd m, rm.ws) ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none) := by
  obtain ⟨h, hres⟩ := node_reach X bl B bnd hok hB hbk m rm hrm
  apply Reach.mem_walk X bl hok h
  rw [ltree_node X bl B bnd hok hB hbk m rm hres hrm, hleaf]

theorem ltree_page' (p : w64) (hin : B.ib.root' ≠ W64 0) (hnm : B.nm !! p = none)
    (pg : List w8) (hpg : X.v.pages !! p.toNat = some pg) :
    ltree X bl p = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  rw [ltree_of_B X bl B bnd hok hB hbk]
  have hr : resolve B p = none := by unfold resolve; rw [if_neg hin]; exact hnm
  rw [hr]
  unfold wpageAt; rw [if_neg hin, hpg]; rfl

/-- The pages below a page position are reached through the pages. -/
theorem own_reach (hin : B.ib.root' ≠ W64 0) {c p : Nat} (h : ownHas X.v.pages c p) :
    ∀ p0 : w64, p0.toNat = c →
      (∀ d, treeHas X.v.pages c d → B.nm !! W64 (d : Int) = none) →
      ∀ b, ∃ b', Reach (ltree X) bl p0 b (W64 (p : Int)) b' ∧ (W64 (p : Int)).toNat = p := by
  induction h with
  | root r pg hpg =>
    intro p0 hp0 _ b; subst hp0
    exact ⟨b, by rw [w64_toNat_eq]; exact Reach.refl _ _, by rw [w64_toNat_eq]⟩
  | child r pg i id hpg hbr hi _ ih =>
    intro p0 hp0 hfree b
    subst hp0
    have hnm : B.nm !! p0 = none := by
      have := hfree p0.toNat (treeHas.root _ pg hpg); rwa [w64_toNat_eq] at this
    have hnl : pageFlags pg ≠ leafPageFlag := by
      rw [hbr]; simp [branchPageFlag, leafPageFlag]
    have hL := ltree_page' X bl B bnd hok hB hbk p0 hin hnm pg hpg
    simp only [hnl, decide_false] at hL
    have hi' : i < (pageWs pg).length := by rw [pageWs_len]; exact hi
    obtain ⟨b', hr, hpn⟩ := ih (W64 (branchPgid pg i : Int)) (branchPgid_toNat pg i)
      (fun d hd => hfree d (treeHas.sub _ pg d hpg (pageHas.child pg i d hbr hi hd)))
      (wEntryBnd b (pageWs pg) i)
    refine ⟨b', Reach.step p0 b (pageWs pg) i _ _ hL hi' ?_, hpn⟩
    rw [pageWs_getD pg i hi, (pageW_branch pg i hnl).2]
    exact hr

/-- **An entry of the bucket is in a block of its walk** (`entryIn`, either kind). -/
theorem entryIn_block (k v : List w8) (h : entryIn X.v B k v) :
    ∃ x ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none), ∃ w ∈ x.2.2,
      w.key = k ∧ isBktFlag w.flags ∧ w.value = v := by
  have hc := wOK_bktClean X hok bl B hB
  rcases h with ⟨m, rm, w, hrm, hleaf, hw, hk, hf, hv⟩ |
    ⟨c, p, pg, i, hpos, hown, hpg, hlf, hi, hk, hf, hv⟩
  · exact ⟨_, leaf_block X bl B bnd hok hB hbk m rm hrm hleaf, w, hw, hk, hf, hv⟩
  · -- the page position `c` is reached, and the pages below it
    have hrch : ∃ p0 b0, p0.toNat = c ∧ B.ib.root' ≠ W64 0 ∧
        (∀ d, treeHas X.v.pages c d → B.nm !! W64 (d : Int) = none) ∧
        Reach (ltree X) bl (X.rootPid bl) (none, none) p0 b0 := by
      have hrp : X.rootPid bl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
      rcases hpos with ⟨hrn, hin, rfl⟩ | ⟨m, j, ⟨rm, w, hrm, hbr, hw, hwp, hnm⟩, hc64⟩
      · refine ⟨B.ib.root', (none, none), rfl, hin, ?_, by rw [hrp]; exact Reach.refl _ _⟩
        intro d _; rw [(hc.2.2.1 hrn).2]; rfl
      · have hin : B.ib.root' ≠ W64 0 := by
          intro h0; have := hc.2.2.2.2.2.2.1 h0 m rm hrm; rw [hbr] at this; cases this
        obtain ⟨hreach, hres⟩ := node_reach X bl B bnd hok hB hbk m rm hrm
        have hL := ltree_node X bl B bnd hok hB hbk m rm hres hrm
        rw [hbr] at hL
        have hj : j < rm.ws.length := (List.getElem?_eq_some_iff.1 hw).1
        have := hreach.snoc rm.ws j hL hj
        have hgw : rm.ws.getD j default = w := by
          rw [List.getD_eq_getElem?_getD, hw]; rfl
        rw [hgw, hwp] at this
        refine ⟨_, _, ?_, hin, ?_, this⟩
        · simp; omega
        · intro d hd
          have hcn : (W64 (c : Int)).toNat = c := by simp; omega
          exact hc.2.2.2.2.2.2.2.2.2.1 m j _ ⟨rm, w, hrm, hbr, hw, hwp, hnm⟩ d (by rw [hcn]; exact hd)
    obtain ⟨p0, b0, hp0, hin, hfree, hreach⟩ := hrch
    obtain ⟨b', hr2, hpn⟩ := own_reach X bl B bnd hok hB hbk hin hown p0 hp0 hfree b0
    have hreach' := hreach.trans hr2
    have hnmp : B.nm !! W64 (p : Int) = none := hfree p (ownHas_treeHas hown)
    have hpg' : X.v.pages !! (W64 (p : Int)).toNat = some pg := by rw [hpn]; exact hpg
    have hL := ltree_page' X bl B bnd hok hB hbk _ hin hnmp pg hpg'
    simp only [hlf, decide_true] at hL
    refine ⟨_, Reach.mem_walk X bl hok hreach' _ hL, pageW pg i, ?_, ?_⟩
    · unfold pageWs; exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    · unfold pageW
      simp only [hlf, if_true]
      exact ⟨hk, isBktFlag_leaf pg i hf, hv⟩

end datareach

end Write

end bbolt
end EtcdGrove
end Perennial
