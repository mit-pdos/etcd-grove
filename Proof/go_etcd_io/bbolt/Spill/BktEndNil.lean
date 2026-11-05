/-
`Bucket.spill`'s root loop's end (U9x5, `notes/bbolt-proof-plan.md`), part 3: **the root bucket's
base tree when it has no root node** (`end_nilTree'`, for `BktEnd.rinv_end_nil`): its tree at its header's
root page is a subtree of the committed tree (`sTree_base`), over the spill's page map (no buffer
yet), its slots base slots.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndTree
public import Proof.go_etcd_io.bbolt.Spill.BktSlot
public import Proof.go_etcd_io.bbolt.Spill.BktEndCov
public import Proof.go_etcd_io.bbolt.Spill.BktEndOwn
public import Proof.go_etcd_io.bbolt.Spill.BktValKey

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section nil
variable [GooseExts]

theorem rootPage_of {X : WX} {B : BRec} (hB : X.t.bs !! X.rl = some B) :
    X.rootPage = B.ib.root'.toNat := by
  unfold WX.rootPage; rw [hB]; rfl

/-- A page of the view lies in the committed tree. -/
theorem treeHas_of_page {C : CommitSt} (hcok : treeOK C) {x : Nat} {pg : List w8}
    (hpg : C.pages !! x = some pg) : treeHas C.pages C.root x := by
  have e : treePages C.pages C.root !! x = some pg := by rw [hcok.2.1]; exact hpg
  rw [treePages_lookup] at e
  split at e
  · assumption
  · cases e

/-- **The root bucket's base tree** (no root node, no buffer): an `sTree` over the spill's page
map at its header's root page, its pages the committed tree's below it. -/
theorem nil_sTree {X : WX} {fl : FLPg} {C : CommitSt} {B0 : BRec} (hpre : spillPre X fl)
    (hB0 : X.t.bs !! X.rl = some B0) (hrn : B0.bv.rootNode' = null)
    (hcp : X.v.pages = C.pages) (hcok : treeOK C) (hhwm : C.hwm ≤ X.t.mv.pgid'.toNat) :
    ∃ h, sTree (spP X) X.t.mv.pgid'.toNat X.rootPage none none h
      (subPages C.pages X.rootPage) := by
  have hok := hpre.1
  have htc := hok.1
  have hP : spP X = X.v.pages := spP_clean htc.2.1.2.1
  have h0 : B0.ib.root' ≠ W64 0 := htc.2.1.2.2.2.2 B0 hB0
  have hcl := (htc.2.2.2.2.2 X.rl B0 hB0).1
  have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat B0.ib.root'.toNat := (hcl.2.1 h0).2 hrn
  obtain ⟨bnd, hbk⟩ := (hok.2.1 X.rl B0 hB0).1
  have hk : treeKeys X.v.pages B0.ib.root'.toNat none none := hbk.1 hrn h0
  rw [rootPage_of hB0, hP]
  obtain ⟨pg, hpg⟩ := treeWF_page_some hwf
  rw [hcp] at hpg hk
  have ht := treeHas_of_page hcok hpg
  obtain ⟨pht, hpht⟩ := hcok.1.2.2.2
  have hs := sTree_base C hcok ht hk pht hpht
  exact ⟨pht _, sTree_agree (fun x _ => by rw [hcp]) hhwm hs⟩

/-- **The base tree's slots are base slots.** -/
theorem nil_slots {X : WX} {C : CommitSt} (hP : spP X = C.pages) (root : Nat) :
    ∀ s ∈ pgSlots (spP X) (subPages C.pages root), s ∈ treeSlots C := by
  intro s hs
  rw [hP] at hs
  unfold pgSlots at hs
  obtain ⟨x, hx, hsx⟩ := List.mem_flatMap.1 hs
  obtain ⟨pg, hpg⟩ := treeHas_page (mem_subPages.1 hx)
  rw [hpg] at hsx
  simp only [List.mem_range'] at hsx
  obtain ⟨i, hi, rfl⟩ := hsx
  exact mem_pagesSlots.2 ⟨x, pg, hpg, by omega, by omega⟩


/-- A bucket entry of the root is an entry of one of its logical leaves. -/
theorem mem_rootEnts_leaf {X : WX} {n v : List w8} (h : (n, v) ∈ rootEnts X) :
    ∃ ws ∈ X.leaves X.rl, ∃ w ∈ ws, isBktFlag w.flags ∧ w.key = n ∧ w.value = v := by
  unfold rootEnts at h
  obtain ⟨ws, hws, hm⟩ := List.mem_flatMap.1 h
  obtain ⟨w, hw, he⟩ := List.mem_filterMap.1 hm
  by_cases hb : isBktFlag w.flags
  · simp only [hb, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at he
    exact ⟨ws, hws, w, hw, hb, he.1, he.2⟩
  · simp [hb] at he

/-- The extents of a bucket are its positions' (`coverW`). -/
theorem coverW_of_extent {X : WX} {bl : Loc} {e : w64 × Nat} {s : Nat}
    (hb : X.t.bs !! bl ≠ none) (he : e ∈ X.extents bl) (h1 : e.1.toNat ≤ s)
    (h2 : s < e.1.toNat + e.2) : ∃ pid, coverW X s (.pos bl pid) := by
  obtain ⟨pid, hp, hpe⟩ := List.mem_filterMap.1 he
  exact ⟨pid, hb, hp, e, hpe, h1, h2⟩

/-- **A bucket without a root node, its root page `0`, covers no slot.** -/
theorem inline_noCover {X : WX} {c : Loc} {Cc : BRec} (hc : X.t.bs !! c = some Cc)
    (hcl : bktClean X.v X.t.mv.pgid'.toNat c Cc) (hrn : Cc.bv.rootNode' = null)
    (h0 : Cc.ib.root' = W64 0) {s : Nat} {pid : w64} (h : coverW X s (.pos c pid)) : False := by
  obtain ⟨-, hp, e, he, -⟩ := h
  have hrp : X.rootPid c = W64 0 := by unfold WX.rootPid; rw [hc]; simp [h0]
  have hpid : pid = W64 0 := by
    unfold WX.positions at hp
    rw [hrp] at hp
    cases hf : X.fuel with
    | zero => rw [hf] at hp; simp [lposF] at hp
    | succ k =>
      rw [hf] at hp
      simp only [lposF, List.mem_cons] at hp
      rcases hp with hp | hp
      · exact hp
      · exfalso
        cases hL : ltree X c (W64 0) with
        | none => rw [hL] at hp; simp at hp
        | some lw =>
          obtain ⟨lf, ws⟩ := lw
          have := ltree_inline_leaf X c Cc hc hcl h0 _ lf ws hL
          subst this
          rw [hL] at hp; simp at hp
  subst hpid
  simp [WX.posExtent, hc, resolve, h0, hrn] at he

/-- **Every base slot is the base tree's or pending** (no root node, every cached child without
one): `spillPre`'s coverage; a covering position is the root's (a page under its root page), a
cached child's (under its value's root, an entry of a root page), or no other bucket's
(`derefPre`, `liveReach`: every bucket the root or a cached child, whose cache is empty); an
unopened bucket's value is an entry of a root page. -/
theorem nil_cover {X : WX} {fl : FLPg} {C : CommitSt} {B0 : BRec} (hpre : spillPre X fl)
    (hreach : liveReach X) (_hfv : flViewU X fl) (hB0 : X.t.bs !! X.rl = some B0)
    (hrn : B0.bv.rootNode' = null)
    (hkids : ∀ k c, B0.bm !! k = some c → ∃ C0, X.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null)
    (hcp : X.v.pages = C.pages) (_hcok : treeOK C) :
    ∀ s ∈ treeSlots C, s ∈ pgSlots (spP X) (subPages C.pages X.rootPage) ∨ s ∈ pendSlots fl := by
  intro s hs
  have hok := hpre.1
  have htc := hok.1
  have hP : spP X = X.v.pages := spP_clean htc.2.1.2.1
  have h0 : B0.ib.root' ≠ W64 0 := htc.2.1.2.2.2.2 B0 hB0
  have hcl := (htc.2.2.2.2.2 X.rl B0 hB0).1
  have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat B0.ib.root'.toNat := (hcl.2.1 h0).2 hrn
  have hnm : B0.nm = ∅ := (hcl.2.2.1 hrn).2
  have hfree : ∀ d, treeHas X.v.pages B0.ib.root'.toNat d → B0.nm !! W64 (d : Int) = none :=
    fun d _ => by rw [hnm]; rfl
  have hrp : X.rootPid X.rl = B0.ib.root' := by unfold WX.rootPid; rw [hB0]; rfl
  -- a page under the root page
  have hin : ∀ id pg, treeHas X.v.pages B0.ib.root'.toNat id → X.v.pages !! id = some pg →
      id ≤ s → s < id + (1 + pageOverflow pg) →
      s ∈ pgSlots (spP X) (subPages C.pages X.rootPage) := by
    intro id pg ht hpg h1 h2
    rw [rootPage_of hB0, hP]
    rw [hcp] at ht hpg ⊢
    exact mem_pgSlots_of (mem_subPages.2 ht) hpg h1 h2
  have hroot : walkCov X X.rl X.fuel (X.rootPid X.rl) s →
      s ∈ pgSlots (spP X) (subPages C.pages X.rootPage) := by
    intro hw
    rw [hrp] at hw
    obtain ⟨id, pg, ht, hpg, h1, h2⟩ := walkCov_pages hB0 h0 X.fuel _ hwf hfree s hw
    exact hin id pg ht hpg h1 h2
  have hcov : coversSlot X.v.pages s := by
    rw [hcp]; exact (mem_pagesSlots_iff C.pages s).1 hs
  refine (hpre.2.2.2.2 s hcov).elim (fun hl => Or.inl ?_) Or.inr
  rcases hl with ⟨bl, e, hbn, he, h1, h2⟩ | ⟨n, v, hmem, -, hbc⟩
  · obtain ⟨pid, hpid⟩ := coverW_of_extent hbn he h1 h2
    obtain ⟨Bl, hBl⟩ := Option.ne_none_iff_exists'.1 hbn
    rcases bkt_root_or_child hok hreach hB0 hBl with rfl | ⟨n, hn⟩
    · obtain ⟨-, hp, e', he', h1', h2'⟩ := hpid
      exact hroot (Or.inl ⟨pid, hp, e', he', h1', h2'⟩)
    · -- a cached child without a root node: its pages are its value's, an entry of a root page
      obtain ⟨C0, hC0, hrn0⟩ := hkids n bl hn
      rw [hBl] at hC0; cases hC0
      obtain ⟨Cc, v, hCc, hent, -, -, -, hib⟩ := (hok.2.1 X.rl B0 hB0).2 n bl hn
      rw [hBl] at hCc; cases hCc
      have hibv := hib hrn0
      have hr : Bl.ib.root'.toNat = inBucketRoot v := by rw [hibv]; rfl
      have hclc := (htc.2.2.2.2.2 bl Bl hBl).1
      by_cases hc0 : Bl.ib.root' = W64 0
      · exact (inline_noCover hBl hclc hrn0 hc0 hpid).elim
      have hwfc : treeWF X.v.pages X.t.mv.pgid'.toNat Bl.ib.root'.toNat := (hclc.2.1 hc0).2 hrn0
      have hnmc : Bl.nm = ∅ := (hclc.2.2.1 hrn0).2
      have hrpc : X.rootPid bl = Bl.ib.root' := by unfold WX.rootPid; rw [hBl]; rfl
      obtain ⟨-, hp, e', he', h1', h2'⟩ := hpid
      obtain ⟨id, pg, ht, hpg, a1, a2⟩ := walkCov_pages hBl hc0 X.fuel Bl.ib.root' hwfc
        (fun d _ => by rw [hnmc]; rfl) s
        (Or.inl ⟨pid, by rw [← hrpc]; exact hp, e', he', h1', h2'⟩)
      have hbh : bucketHas X.v.pages v id := by
        rw [hr] at ht
        exact bucketHas.file v id (by rw [← hr]; intro e0; exact hc0 (by
          apply BitVec.eq_of_toNat_eq; rw [e0]; rfl)) ht
      rcases hent with ⟨l, r, -, hr0, -⟩ | ⟨c0, p, ppg, i, hpr, hown, hppg, hfl, hi, -, hf, hval⟩
      · rw [(hcl.2.2.1 hrn).1] at hr0; cases hr0
      · have hc0r : c0 = B0.ib.root'.toNat := by
          rcases hpr with ⟨-, -, rfl⟩ | ⟨l, k, ⟨r, -, hr0, -⟩, -⟩
          · rfl
          · rw [(hcl.2.2.1 hrn).1] at hr0; cases hr0
        subst hc0r
        rw [← hval] at hbh
        exact hin id pg (treeHas_trans (treeHas_of_ownHas hown)
          (treeHas_bucket hppg hfl hi hf hbh)) hpg a1 a2
  · obtain ⟨ws, hws, w, hw, hbk, -, rfl⟩ := mem_rootEnts_leaf hmem
    exact hroot (Or.inr ⟨ws, hws, w, hw, hbk, hbc⟩)

end nil

end Spill

end bbolt
end EtcdGrove
end Perennial
