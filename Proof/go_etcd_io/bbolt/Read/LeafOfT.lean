/-
U6 (`notes/bbolt-proof-plan.md`): R6's `ltree_leaf_of_T` (`Model/LTree`), corrected and proved as
`ltree_leaf_of_T'`. The shared statement is false: it takes any position `pid` whose logical entry
is a leaf, and `ltree X bl pid` reads any page of the view at a position bucket `bl` does not reach
(e.g. a leaf page of another top-level bucket), whose entries are not `bl`'s. The corrected
statement adds that the leaf is one of the bucket's walk (`ws ∈ X.leaves bl`); then its plain
entries are those of the bucket's data within the bounds the walk gives it (`Write.bInv_walk`:
each block's keys within its bounds, the bounds pairwise disjoint).
-/
module

public import Proof.go_etcd_io.bbolt.Write.Data
public import Proof.go_etcd_io.bbolt.Write.DataBkt
public import Proof.go_etcd_io.bbolt.Read.LRoutes
public import Proof.go_etcd_io.bbolt.Read.Ents

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace LeafT

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write Ents

section leafOfT
variable [GooseExts]

/-- A leaf of a well-formed writer's logical tree is sorted. -/
theorem leaf_pw (X : WX) (hok : wOK X) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B)
    (p : w64) (ws : List WEntry) (hL : ltree X bl p = some (true, ws)) : wsPw ws := by
  have hc := wOK_bktClean X hok bl B hB
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  unfold ltree at hL
  rw [hB] at hL
  simp only at hL
  cases hr : resolve B p with
  | some l =>
    rw [hr] at hL
    simp only at hL
    cases hrl : B.ns !! l with
    | none => rw [hrl] at hL; cases hL
    | some r =>
      rw [hrl] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      rw [← hL.2]
      exact wsSorted_pw _ (hc.2.2.2.2.2.2.2.1 l r hrl).2.2.2.1
  | none =>
    rw [hr] at hL
    simp only at hL
    cases hp : wpageAt X.v B p with
    | none => rw [hp] at hL; cases hL
    | some x =>
      obtain ⟨pa, pg⟩ := x
      rw [hp] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
      obtain ⟨hfl, rfl⟩ := hL
      by_cases hin : B.ib.root' = W64 0
      · have hrn : B.bv.rootNode' = null := by
          unfold resolve at hr; rw [if_pos hin] at hr; split at hr
          · assumption
          · cases hr
        have hg := (hc.1 hin hrn).2.2.1
        unfold wpageAt at hp; rw [if_pos hin] at hp
        split at hp
        · simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨-, rfl⟩ := hp
          exact LR.pageWs_pw _ hg.2.1 hg.2.2.1.2.2.2
        · cases hp
      · have hpg : X.v.pages !! p.toNat = some pg := by
          unfold wpageAt at hp; rw [if_neg hin] at hp
          cases h : X.v.pages !! p.toNat with
          | none => rw [h] at hp; cases hp
          | some pg' => rw [h] at hp; simp only [Option.map_some, Option.some.injEq,
                          Prod.mk.injEq] at hp; rw [hp.2]
        exact LR.pageWs_pw pg hfl (LR.viewWF_leaf_sorted X.v hv _ pg hpg hfl)

theorem plain_pw (ws : List WEntry) (hs : wsPw ws) : esSorted (ws.filterMap plainOf) := by
  unfold esSorted
  apply List.Pairwise.filterMap _ _ hs
  intro a a' hlt b hb b' hb'
  rw [plainOf_key a b hb, plainOf_key a' b' hb']
  exact hlt

end leafOfT

end LeafT

open Classical in
open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write Ents LeafT in
/-- **`ltree_leaf_of_T`** (`Model/LTree`), corrected (`hw`: the leaf is one of the bucket's walk)
and proved: the plain entries of a logical leaf of bucket `n` are the entries of
`bktEnts (T.cur n)` within the leaf's bounds. -/
theorem ltree_leaf_of_T' [GooseExts] (X : WX) (n : GoString) (bl : Loc) (pid : w64)
    (ws : List WEntry) (hok : wOK X) (hb : bktLoc X n = some bl)
    (hl : ltree X bl pid = some (true, ws)) (hw : ws ∈ X.leaves bl) :
    ∃ lo hi, ws.filterMap (fun w => if decide (isBktFlag w.flags) then none
        else some (w.key, w.value)) =
      (bktEnts (((wtxData X) !! n).getD ∅)).filter fun e => decide (keyIn lo hi e.1) := by
  -- the bucket's record
  have hB : ∃ B, X.t.bs !! bl = some B := by
    unfold bktLoc at hb
    cases hR : X.t.bs !! X.rl with
    | none => rw [hR] at hb; cases hb
    | some R =>
      rw [hR] at hb
      simp only [Option.bind_some] at hb
      exact Option.isSome_iff_exists.1 ((hok.1.2.2.2.2.2 X.rl R hR).2 n bl hb)
  obtain ⟨B, hB⟩ := hB
  obtain ⟨bnd, hbk⟩ := (hok.2.1 bl B hB).1
  obtain ⟨hP1, -, hP2⟩ := bInv_walk X bl B bnd hok hB hbk X.fuel _ _
    (bInv_root X bl B bnd hok hB hbk)
  -- the leaf's block
  have hws : ∃ x ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none), x.2.2 = ws := by
    unfold WX.leaves at hw
    rw [← lleavesB_snd] at hw
    obtain ⟨x, hx, e⟩ := List.mem_map.1 hw
    exact ⟨x, hx, e⟩
  obtain ⟨x, hx, rfl⟩ := hws
  refine ⟨x.2.1.1, x.2.1.2, ?_⟩
  -- the bucket's data
  have hdata : ((wtxData X) !! n).getD ∅ = GMap.ofList (lbktEnts X bl) := by
    rw [wtxData_lookup]
    unfold bktData
    obtain ⟨v0, hv0⟩ := bktLoc_rootEnt X hok n bl hb
    cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 hf (n, v0) hv0
      simp at this
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      rw [bktDataOf_eq, hb]
  rw [hdata]
  have hE := lbktEnts_blocks X bl
  have hsortB : ∀ y ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none), wsPw y.2.2 :=
    fun y hy => leaf_pw X hok bl B hB y.1 y.2.2 (lleavesB_leaf _ _ _ _ _ y hy)
  have hnd : (lbktEnts X bl).Pairwise (fun a b => a.1 ≠ b.1) := by
    rw [hE, List.pairwise_flatMap]
    refine ⟨fun y hy => ?_, ?_⟩
    · apply (plain_pw _ (hsortB y hy)).imp
      intro a b hab e
      rw [e] at hab
      exact go.goStringLt_irrefl _ hab
    · apply List.Pairwise.imp_of_mem _ hP2
      intro y z hy hz hR e he e' he' heq
      obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.1 he
      obtain ⟨w', hw', hwe'⟩ := List.mem_filterMap.1 he'
      have h1 := hP1 y hy w hw
      have h2 := hP1 z hz w' hw'
      rw [← plainOf_key w e hwe, heq, plainOf_key w' e' hwe'] at h1
      exact hR _ h1 h2
  show x.2.2.filterMap plainOf = _
  apply sorted_ext
  · exact plain_pw _ (hsortB x hx)
  · exact (bktEnts_sorted _).filter _
  · intro e
    rw [List.mem_filter, mem_bktEnts, ofList_lookup_iff _ hnd, decide_eq_true_iff]
    constructor
    · intro he
      obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.1 he
      refine ⟨?_, ?_⟩
      · rw [hE]; exact List.mem_flatMap.2 ⟨x, hx, he⟩
      · rw [plainOf_key w e hwe]; exact hP1 x hx w hw
    · rintro ⟨hm, hk⟩
      rw [hE] at hm
      obtain ⟨y, hy, hey⟩ := List.mem_flatMap.1 hm
      have hyx : y = x := by
        apply Classical.byContradiction
        intro hne
        obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.1 hey
        have h1 := hP1 y hy w hw
        rw [← plainOf_key w e hwe] at h1
        exact pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hP2 y hy x hx hne _ h1 hk
      rw [← hyx]; exact hey
