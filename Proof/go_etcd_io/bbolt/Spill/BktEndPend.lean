/-
`Bucket.spill`'s ends (U9w6, `notes/bbolt-proof-plan.md`): **the written tree's slots are not
pending, and the new mark's slots are buffers** (`Bucket.spill.spec`'s two last success facts,
maintainer 13's queue (a)).

- The slots of an owned set are not pending (`slotInv_notPend`). At the root spill's exit the
  written tree's slots are the root tree's `D'`, owned (`spDone`'s `slotInv`), so not pending
  (`root_notPend`): no clause on which slots the steps free is needed.
- With no root node (`end_nil_notPend`), nothing changed (`RInv.same`): a slot of the root's base
  tree is a root position's (covered by the logical tree, so not pending by `flView`) or in a
  nested bucket's tree (owned, `ent_class`).
- `markCov` follows from the start's and the steps' `markGrow` (`markCov_grow`).
- (U9w7) The buffers' slots are free at the start or at or above the committed mark
  (`bufSlots_src`, from `RInv.src`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndDisj
public import Proof.go_etcd_io.bbolt.Spill.BktEndNilEls
public import Proof.go_etcd_io.bbolt.Spill.BktEndShape
public import Proof.go_etcd_io.bbolt.Spill.BktFinal
public import Proof.go_etcd_io.bbolt.Txn.WInit
public import Proof.go_etcd_io.bbolt.Commit.MarkCov

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section pend
variable [GooseExts]

/-- **An owned slot is not pending** (`slotInv`: no owned slot is a freelist id). -/
theorem slotInv_notPend {fl : FLPg} {hwm : Nat} {L : List Nat} (h : slotInv fl hwm L) {s : Nat}
    (hs : s ∈ L) : s ∉ pendSlots fl := by
  intro hp
  obtain ⟨z, hz, hze⟩ := List.mem_map.1 hp
  have h3 := h.2.1 s hs
  have e : W64 (s : Int) = z := BitVec.eq_of_toNat_eq (by rw [w64_toNat_of_lt h3.2.1, hze])
  exact h3.2.2 (by rw [e]; exact List.mem_append_right _ hz)

/-- **`markCov` through a growth of the buffers over the mark's.** -/
theorem markCov_grow {X X' : WX} {hwm : Nat} (h : markCov X hwm) (hg : markGrow X X') :
    markCov X' hwm := by
  intro s h1 h2
  have key : ∃ id pg, X'.t.bufs !! id = some pg ∧ id.toNat ≤ s ∧
      s < id.toNat + (1 + pageOverflow pg) := by
    by_cases hs : s < X.t.mv.pgid'.toNat
    · have hm := h s h1 hs
      unfold bufSlots at hm
      simp only [List.mem_flatMap, List.mem_range'] at hm
      obtain ⟨⟨id, pg⟩, he, i, hi, rfl⟩ := hm
      exact ⟨id, pg, hg.1 id pg ((GMap.mem_toList _ id pg).1 he), by simp only; omega,
        by simp only at hi ⊢; omega⟩
    · exact hg.2 s (Nat.le_of_not_lt hs) h2
  obtain ⟨id, pg, hb, a1, a2⟩ := key
  unfold bufSlots
  simp only [List.mem_flatMap, List.mem_range']
  exact ⟨(id, pg), (GMap.mem_toList _ id pg).2 hb, s - id.toNat, by dsimp only; omega,
    by dsimp only; omega⟩

/-- **The buffer slots' source** (U9w7, `Bucket.spill.spec`'s last success fact): from `bufSrc`
(`RInv.src`), every slot of `bufSlots` free in `F` or at or above a lower mark. -/
theorem bufSlots_src {X : WX} {F : List w64} {hwm hwm' : Nat} (h : bufSrc X F hwm)
    (hle : hwm' ≤ hwm) : ∀ s ∈ bufSlots X.t.bufs, W64 s ∈ F ∨ hwm' ≤ s := by
  intro s hs
  unfold bufSlots at hs
  simp only [List.mem_flatMap, List.mem_range'] at hs
  obtain ⟨⟨id, pg⟩, he, i, hi, rfl⟩ := hs
  rcases h id pg ((GMap.mem_toList _ id pg).1 he) i hi with h' | h'
  · left; simp only [Nat.one_mul]; exact h'
  · right; simp only [Nat.one_mul]; omega

/-- **At the root spill's exit, the written tree's slots are not pending**: they are the root
tree's (`sTree_slots`), owned. -/
theorem root_notPend {X2 : WX} {w2 : WDb} {C : CommitSt} {rl rt : Loc} {B1 : BRec} {rr : NRec}
    {S D' O : List Nat} {h' hwm : Nat} (hrl : X2.rl = rl) (hcp : C.pages = X2.v.pages)
    (hsT : sTree (spP X2) X2.t.mv.pgid'.toNat rr.nv.pgid'.toNat none none h' S)
    (hD' : D' = pgSlots (spP X2) S) (hsi : slotInv w2.fl hwm (O ++ D')) :
    ∀ s ∈ treeSlots (spillC (X2.setBkt rl (bkRooted B1 rt rr.nv.pgid')) C.pages),
      s ∉ pendSlots w2.fl := by
  intro s hs
  have e : (spillC (X2.setBkt rl (bkRooted B1 rt rr.nv.pgid')) C.pages).pages =
      treePages (spP X2) rr.nv.pgid'.toNat := by
    show treePages ((X2.setBkt rl (bkRooted B1 rt rr.nv.pgid')).bufPages ∪ C.pages)
      (X2.setBkt rl (bkRooted B1 rt rr.nv.pgid')).rootPage = _
    rw [setBkt_rootPage_of hrl, hcp]; rfl
  unfold treeSlots at hs
  rw [e] at hs
  have hm := (sTree_slots hsT s).2 hs
  rw [← hD'] at hm
  exact slotInv_notPend hsi (List.mem_append_right _ hm)

/-- **With no root node, the base tree's slots are not pending at the end**: nothing changed; a
root position's slot is covered by the logical tree (`nilBkt_coverW`), so not pending (`flView`);
a nested bucket's slot is owned (`ent_class`). -/
theorem end_nil_notPend {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' = null)
    (hvC : X.v = View.ofC X.v.base w.C) :
    ∀ s ∈ treeSlots (spillC X w0.C.pages), s ∉ pendSlots w.fl := by
  have hnv : ∀ k ∈ keys, ∀ v p, ks k ≠ .val v p := by
    intro k hkm v p he
    cases p with
    | true => exact hI.putRoot ⟨k, v, he⟩ B hB hrn
    | false =>
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hkm
      have hjl : j < keys.length := (List.getElem?_eq_some_iff.1 hj).1
      exact ((hks j k hj).1 hjl).2 v he
  have hI' := hI
  obtain ⟨rfl, rfl, rfl⟩ := hI.same hnv
  rw [hB0] at hB; cases hB
  have hok := hpre.1
  have htc := hok.1
  have hP : spP X = X.v.pages := spP_clean htc.2.1.2.1
  have h0 : B0.ib.root' ≠ W64 0 := htc.2.1.2.2.2.2 B0 hB0
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B0 := (htc.2.2.2.2.2 X.rl B0 hB0).1
  have hrt : rtOK X X.rl := hpre.2.2.2.1 X.rl (by rw [hB0]; simp)
  have hcp : w.C.pages = X.v.pages := by
    have := congrArg View.pages hvC; simpa [View.ofC] using this.symm
  have h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp
    have := hI'.cok.2.2.2.1 p pg (by rw [hcp]; exact hp)
    have := hI'.hwm0
    have := X.t.mv.pgid'.isLt
    omega
  obtain ⟨h, hS⟩ := nil_sTree hpre hB0 hrn hcp.symm hI'.cok hI'.hwm0
  have hrP : X.rootPage = B0.ib.root'.toNat := rootPage_of hB0
  intro s hs hp
  have hs' : s ∈ pgSlots (spP X) (subPages w.C.pages X.rootPage) := by
    apply (sTree_slots hS s).2
    have e : (spillC X w.C.pages).pages = treePages (spP X) X.rootPage := by
      show treePages (X.bufPages ∪ w.C.pages) X.rootPage = _
      rw [hcp]; rfl
    unfold treeSlots at hs; rw [e] at hs; exact hs
  rw [hP, hcp, hrP] at hs'
  unfold pgSlots at hs'
  obtain ⟨x, hx, hsx⟩ := List.mem_flatMap.1 hs'
  have htx : treeHas X.v.pages B0.ib.root'.toNat x := mem_subPages.1 hx
  obtain ⟨pg, hpg⟩ := treeHas_page htx
  rw [hpg] at hsx
  simp only [List.mem_range'] at hsx
  obtain ⟨j, hj, rfl⟩ := hsx
  rw [Nat.one_mul] at hp
  have hcov : coversSlot X.v.pages (x + j) := ⟨x, pg, hpg, by omega, by omega⟩
  rcases treeHas_split X.v.pages htx with hown | ⟨L, pgL, i, hL, hpL, hl, hi, hbf, hb⟩
  · -- a root position's page: covered by the logical tree
    have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat B0.ib.root'.toNat := (hcl.2.1 h0).2 hrn
    have hwfx := Read.treeHas_treeWF X.v.pages _ htx hwf
    have h2x : 2 ≤ x := by cases hwfx with | page _ _ h _ _ _ _ _ => exact h
    have hcw := nilBkt_coverW (s := x + j) hB0 (hcl.2.2.1 hrn).2 h0 hrt hown h2x (h64 x pg hpg)
      hpg (by omega) (by omega)
    exact ((hfv.1.1 _ hcov).1 (lCovers_of_coverW hcw)) hp
  · -- a nested bucket's page: owned
    have hpr : posRoot B0 B0.ib.root'.toNat := Or.inl ⟨hrn, h0, rfl⟩
    have hwA := mem_allEnts_page hok hreach hrt hB0 h64 hpr hL hpL hl hi
    have e := mat_pageW_leaf pgL i hl
    have hbk : isBktFlag (pageW pgL i).flags := by
      rw [e.1]; exact isBkt_of_lowBit (leafFlags_lt pgL i) hbf
    have hm := rootEnts_of_allEnts hwA hbk
    rw [e.2.2.1, e.2.2.2] at hm
    have hbc : bucketCovers (spP X) (leafValue pgL i) (x + j) := by
      rw [hP]; exact ⟨x, pg, hb, hpg, by omega, by omega⟩
    have hown : x + j ∈ Lroot ++ keys.flatMap Dc := by
      rcases ent_class hpre hreach hfv hB0 hk hI' hks hvC hm hbc with ⟨hkk, hd⟩ | ⟨-, hl'⟩
      · exact List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hkk, hd⟩)
      · exact List.mem_append_left _ hl'
    exact slotInv_notPend hI'.slots hown hp

end pend

end Spill

end bbolt
end EtcdGrove
end Perennial
