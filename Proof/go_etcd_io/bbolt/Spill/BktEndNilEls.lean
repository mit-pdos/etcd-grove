/-
`Bucket.spill`'s root loop's end (U9x10, `notes/bbolt-proof-plan.md`; moved from `Spill/BktEndNil`):
**the root bucket's base tree, with no root node, gives the root shape and the writer's data**
(`nil_els`) and the tree at the end (`end_nilTree'`, for `BktEnd.rinv_end_nil`). Its elements are
the entries of its view leaf pages under its root page, a page position (`posShape`: bucket
entries within the bounds); its names its logical leaves' (`BktEndOld.nilBkt_leavesR`); a value's
data an unopened bucket's (`oldU`) or a cached child's without a root node (`oldN`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndOld

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section nil
variable [GooseExts]

/-- **The base tree's elements give the root shape and the writer's data** (see the module doc). -/
theorem nil_els {X : WX} {fl : FLPg} {C : CommitSt} {B0 : BRec} (hpre : spillPre X fl)
    (hreach : liveReach X) (hB0 : X.t.bs !! X.rl = some B0) (hrn : B0.bv.rootNode' = null)
    (hkids : ∀ k c, B0.bm !! k = some c → ∃ C0, X.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null)
    (hnr : ∀ k c, B0.bm !! k = some c → c ≠ X.rl)
    (hcp : X.v.pages = C.pages) (hcok : treeOK C) (hhwm : C.hwm ≤ X.t.mv.pgid'.toNat) :
    endEls X (spP X) (pgSlots (spP X) (subPages C.pages X.rootPage))
      (treeEls (spP X) X.rootPage) := by
  classical
  have hok := hpre.1
  have htc := hok.1
  have hP : spP X = X.v.pages := spP_clean htc.2.1.2.1
  have h0 : B0.ib.root' ≠ W64 0 := htc.2.1.2.2.2.2 B0 hB0
  have hrt : rtOK X X.rl := hpre.2.2.2.1 X.rl (by rw [hB0]; simp)
  have h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp
    have := hcok.2.2.2.1 p pg (by rw [← hcp]; exact hp)
    have := X.t.mv.pgid'.isLt
    omega
  obtain ⟨h, hs⟩ := nil_sTree hpre hB0 hrn hcp hcok hhwm
  have hrP : X.rootPage = B0.ib.root'.toNat := rootPage_of hB0
  rw [hP, hrP] at hs ⊢
  have hpos : posRoot B0 B0.ib.root'.toNat := Or.inl ⟨hrn, h0, rfl⟩
  have hshape := fun {p : Nat} {pg : List w8} => hok.1.2.1.2.2.2.1 X.rl B0 hB0 _ p pg hpos
  -- an element's facts
  have hel : ∀ e ∈ treeEls X.v.pages B0.ib.root'.toNat, e.1 % 2 = bucketLeafFlag ∧
      (0 < e.2.1.length ∧ e.2.1.length ≤ maxKeySize) ∧
      e.2.1.length + e.2.2.length ≤ bboltEntryMax := by
    intro e he
    obtain ⟨id, pg, i, -, ho, hp, hfl, hi, rfl, hkl, hvl⟩ := treeEls_srcWF hs he
    have hsh := hshape ho hp hfl i hi
    refine ⟨hsh.1.2 rfl, ⟨?_, ?_⟩, ?_⟩
    · show 0 < (leafKey pg i).length; rw [hkl]; exact hsh.2.1.1
    · show (leafKey pg i).length ≤ maxKeySize; rw [hkl]; exact hsh.2.2.1 rfl
    · show (leafKey pg i).length + (leafValue pg i).length ≤ bboltEntryMax
      rw [hkl, hvl]; exact hsh.2.1.2
  -- the names
  have hbkP : ∀ pg ∈ treeLeaves X.v.pages B0.ib.root'.toNat, pageFlags pg = leafPageFlag ∧
      ∀ w ∈ pageWs pg, isBktFlag w.flags := by
    intro pg hpg
    obtain ⟨id, -, -, ho, hp, hfl, -, -⟩ := leavesF_page _ _ _ _ _ _ hs.wf hs.keys pg hpg
    refine ⟨hfl, fun w hw => ?_⟩
    unfold pageWs at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi
    rw [(mat_pageW_leaf pg i hfl).1]
    exact isBkt_of_lowBit (leafFlags_lt pg i) ((hshape ho hp hfl i hi).1.2 rfl)
  have hleaves := nilBkt_leavesR hok hB0 hrn h0
  have hnames : (treeEls X.v.pages B0.ib.root'.toNat).map (fun e => e.2.1) =
      (rootEnts X).map Prod.fst := by
    unfold rootEnts treeEls
    rw [hleaves, List.flatMap_map, List.map_flatMap, List.map_flatMap]
    apply Write.flatMap_congr'
    intro pg hpg
    obtain ⟨hfl, hall⟩ := hbkP pg hpg
    rw [filterMap_bkt_keys _ hall]
    unfold pageWs
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro i _
    simp [pageW, hfl]
  -- the values
  have hval : ∀ e ∈ treeEls X.v.pages B0.ib.root'.toNat,
      elVal X X.v.pages (pgSlots X.v.pages (subPages C.pages B0.ib.root'.toNat)) e := by
    intro e he
    obtain ⟨id, pg, i, hpgL, ho, hp, hfl, hi, rfl, -, -⟩ := treeEls_srcWF hs he
    have hbf : leafFlags pg i % 2 = bucketLeafFlag := (hshape ho hp hfl i hi).1.2 rfl
    have hm : (leafKey pg i, leafValue pg i) ∈ rootEnts X := by
      unfold rootEnts
      rw [hleaves]
      refine List.mem_flatMap.2 ⟨pageWs pg, List.mem_map_of_mem hpgL, ?_⟩
      refine List.mem_filterMap.2 ⟨pageW pg i, ?_, ?_⟩
      · unfold pageWs; exact List.mem_map_of_mem (List.mem_range.2 hi)
      · have hb := (hbkP pg hpgL).2 _ (by unfold pageWs; exact List.mem_map_of_mem (List.mem_range.2 hi))
        have e := mat_pageW_leaf pg i hfl
        rw [if_pos (decide_eq_true hb), e.2.2.1, e.2.2.2]
    have hbd := bktData_mem hok hB0 h0 hm
    have hSD : ∀ hwmv Sv, bvalS X.v.pages hwmv (leafValue pg i) Sv →
        ∀ x ∈ Sv, x ∈ pgSlots X.v.pages (subPages C.pages B0.ib.root'.toNat) := by
      intro hwmv Sv hS x hx
      obtain ⟨pgx, hpgx⟩ := bvalS_page hS hx
      have ht : treeHas X.v.pages B0.ib.root'.toNat x :=
        treeHas_trans (treeHas_of_ownHas ho) (treeHas_bucket hp hfl hi hbf ((bvalS_has hS x).2 hx))
      rw [hcp] at ht
      exact mem_pgSlots_of (mem_subPages.2 ht) hpgx (Nat.le_refl _) (by omega)
    cases hbm : B0.bm !! leafKey pg i with
    | none =>
      obtain ⟨hwmv, Sv, hS, hd⟩ := oldU hok hcok hcp hB0 h0 hm hbm
      refine ⟨hwmv, Sv, _, hS, hSD hwmv Sv hS, hd, ?_⟩
      show bktData X (leafKey pg i) = _
      rw [hbd]; simp only [bktDataOf, hB0, Option.bind_some, hbm]; rfl
    | some c =>
      obtain ⟨C0, hC0, hrn0⟩ := hkids _ c hbm
      obtain ⟨hwmv, Sv, hS, hd⟩ :=
        oldN hok hreach hcok hcp hB0 h0 hrt h64 hm hbm hC0 hrn0 (hnr _ c hbm)
      refine ⟨hwmv, Sv, _, hS, hSD hwmv Sv hS, hd, ?_⟩
      show bktData X (leafKey pg i) = _
      rw [hbd]; simp only [bktDataOf, hB0, Option.bind_some, hbm]
  exact endEls_of hel hval hnames

/-- **The root bucket's base tree at the end with no root node** (`end_nilTree`'s statement). -/
theorem end_nilTree' {X0 : WX} {w0 : WDb} {B0 : BRec}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hrn : B0.bv.rootNode' = null)
    (hkids : ∀ k c, B0.bm !! k = some c →
      ∃ C0, X0.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null)
    (hnr : ∀ k c, B0.bm !! k = some c → c ≠ X0.rl)
    (hvC : X0.v = View.ofC X0.v.base w0.C) (hcok : treeOK w0.C)
    (hhwm : w0.C.hwm ≤ X0.t.mv.pgid'.toNat) :
    ∃ h S, sTree (spP X0) X0.t.mv.pgid'.toNat X0.rootPage none none h S ∧
      (∀ s ∈ treeSlots w0.C, s ∈ pgSlots (spP X0) S ∨ s ∈ pendSlots w0.fl) ∧
      (∀ s ∈ pgSlots (spP X0) S, s ∈ treeSlots w0.C) ∧
      endEls X0 (spP X0) (pgSlots (spP X0) S) (treeEls (spP X0) X0.rootPage) := by
  have hcp : X0.v.pages = w0.C.pages := by
    have := congrArg View.pages hvC; simpa [View.ofC] using this
  obtain ⟨h, hs⟩ := nil_sTree hpre hB0 hrn hcp hcok hhwm
  have hP : spP X0 = w0.C.pages := by rw [spP_clean hpre.1.1.2.1.2.1, hcp]
  exact ⟨h, _, hs, nil_cover hpre hreach hfv hB0 hrn hkids hcp hcok, nil_slots hP _,
    nil_els hpre hreach hB0 hrn hkids hnr hcp hcok hhwm⟩

end nil

end Spill

end bbolt
end EtcdGrove
end Perennial
