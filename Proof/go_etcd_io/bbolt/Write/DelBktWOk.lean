/-
U7p (`notes/bbolt-proof-plan.md`): **`DeleteBucket`'s middle records are well-formed**
(`wOK_delMid`, for `Write/DelBktWp`): after `delete(b.buckets, key)` the root's record
no longer caches `n`, the child `c` is dead (out of `bs` and `liveB`, its nodes dead, `killBkt`) and
its dead record replaced (`setDead`). The root's entry `n` is no longer opened: its value is the
cached child's (`bktNested`; one entry per key, `WOpen.allEnts_key_inj`), so it is a good bucket
value whose tree has its keys (`bktClean`'s and `nodeKeys`' unopened clauses). The root's cache
names `c` at `n` only (`gensOK_bktLoc_inj`), and a bucket other than the root caches nothing (its
entries are plain, `leafShape`/`posShape`), so the remaining caches name live buckets.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WOpenWOK
public import Proof.go_etcd_io.bbolt.Spill.BktEndVals
public import Proof.go_etcd_io.bbolt.Write.DelBktKill
public import Proof.go_etcd_io.bbolt.Write.WalkDeadDefs
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsBkt

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section wok
variable [GooseExts]

/-- The records after `delete(b.buckets, key)` (the root's record `R1` without `n`), the child `c`
(record `C`) dead, its dead record `D`. -/
def delMid (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec) : WX :=
  ((X1.setBkt X1.rl (bUnopen R1 n)).killBkt c C).setDead c D

theorem setDead_setDead (X : WX) (c : Loc) (D D' : BRec) :
    (X.setDead c D).setDead c D' = X.setDead c D' := by
  unfold WX.setDead
  simp only [GMap.insert_insert]

theorem delMid_setDead (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D D' : BRec) :
    (delMid X1 c C R1 n D).setDead c D' = delMid X1 c C R1 n D' := by
  unfold delMid; rw [setDead_setDead]

theorem delMid_bs (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec) (k : Loc) :
    (delMid X1 c C R1 n D).t.bs !! k =
      if c = k then none else if k = X1.rl then some (bUnopen R1 n) else X1.t.bs !! k := by
  unfold delMid WX.setDead
  show ((X1.setBkt X1.rl (bUnopen R1 n)).killBkt c C).t.bs !! k = _
  rw [killBkt_bs]
  split
  · rfl
  · unfold WX.setBkt; simp only
    by_cases hk : k = X1.rl
    · subst hk; rw [if_pos rfl, GMap.lookup_insert]
    · rw [if_neg hk, GMap.lookup_insert_ne _ _ (Ne.symm hk)]

theorem delMid_back (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (hcr : c ≠ X1.rl) (k : Loc) (B : BRec) (h : (delMid X1 c C R1 n D).t.bs !! k = some B) :
    k ≠ c ∧ ((k = X1.rl ∧ B = bUnopen R1 n) ∨ (k ≠ X1.rl ∧ X1.t.bs !! k = some B)) := by
  rw [delMid_bs] at h
  by_cases hk : c = k
  · rw [if_pos hk] at h; cases h
  rw [if_neg hk] at h
  refine ⟨Ne.symm hk, ?_⟩
  by_cases hr : k = X1.rl
  · rw [if_pos hr] at h; cases h; exact Or.inl ⟨hr, rfl⟩
  · rw [if_neg hr] at h; exact Or.inr ⟨hr, h⟩

theorem delMid_live (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec) (l : Loc) :
    l ∈ (delMid X1 c C R1 n D).live ↔ l ∈ X1.live ∧ C.ns !! l = none :=
  killBkt_live _ c C l

theorem delMid_liveB (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec) (b : Loc) :
    b ∈ (delMid X1 c C R1 n D).liveB ↔ b ≠ c ∧ b ∈ X1.liveB := by
  show (GMap.delete c X1.liveB !! b).isSome ↔ _
  rw [GMap.lookup_delete_iff]
  by_cases h : c = b
  · subst h; simp
  · rw [if_neg h]; exact ⟨fun h' => ⟨Ne.symm h, h'⟩, fun h' => h'.2⟩

theorem delMid_deadB (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec) (k : Loc) :
    (delMid X1 c C R1 n D).t.deadB !! k = if c = k then some D else X1.t.deadB !! k := by
  show ((X1.t.deadB.insert c { C with ns := ∅ }).insert c D) !! k = _
  by_cases h : c = k
  · subst h; rw [if_pos rfl, GMap.lookup_insert]
  · rw [if_neg h, GMap.lookup_insert_ne _ _ h, GMap.lookup_insert_ne _ _ h]

/-- `bktClean` without the cache entry `n`, when the unopened entries of key `n` hold good bucket
values. -/
theorem bktClean_unopen (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (n : GoString)
    (hc : bktClean v hwm bl B)
    (hbv : ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, isBktFlag w.flags →
      w.key = n → bvalOK v.pages hwm w.value) :
    bktClean v hwm bl (bUnopen B n) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := hc
  refine ⟨c1, c2, c3, c4, c5, c6, c7, fun l r hr => ?_, c9, c10,
    fun k c' e => c11 k c' ((GMap.lookup_delete_Some _ _ _ _).1 e).2⟩
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩ := c8 l r hr
  refine ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11,
    fun hl w hw hf => ⟨fun hs => ?_, (n12 hl w hw hf).2⟩, n13, n14, n15, n16, n17⟩
  by_cases hk : w.key = n
  · exact hbv l r hr hl w hw hf hk
  · apply (n12 hl w hw hf).1
    rw [← hs]
    show (B.bm !! w.key).isSome = ((GMap.delete n B.bm) !! w.key).isSome
    rw [GMap.lookup_delete_ne _ (fun e => hk e.symm)]

/-- `bktKeys` without the cache entry `n`, when the unopened entries of key `n` have their trees'
keys. -/
theorem bktKeys_unopen (v : View) (B : BRec) (n : GoString) (hk : bktKeys v B)
    (htk : ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, isBktFlag w.flags →
      w.key = n → inBucketRoot w.value ≠ 0 → treeKeys v.pages (inBucketRoot w.value) none none) :
    bktKeys v (bUnopen B n) := by
  obtain ⟨bnd, k1, k2, k3⟩ := hk
  refine ⟨bnd, k1, k2, fun l r hr => ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := k3 l r hr
  refine ⟨m1, m2, m3, m4, m5, fun hl w hw hf hroot hno => ?_⟩
  by_cases hkn : w.key = n
  · exact htk l r hr hl w hw hf hkn hroot
  · refine m6 hl w hw hf hroot fun ho => hno ?_
    unfold opened at ho ⊢
    show ((GMap.delete n B.bm) !! w.key).isSome
    rw [GMap.lookup_delete_ne _ (fun e => hkn e.symm)]; exact ho

/-- **A bucket other than the root caches no child** (its entries are plain). -/
theorem bm_nonroot (X : WX) (hok : wOK X) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B)
    (hne : bl ≠ X.rl) (k : GoString) (c : Loc) (h : B.bm !! k = some c) : False := by
  obtain ⟨C, v, -, hent, -⟩ := (hok.2.1 bl B hB).2 k c h
  rcases hent with ⟨l, r, w, hr, hl, hw, -, hbk, -⟩ |
    ⟨c0, p, pg, i, hpr, hown, hpg, hfl, hi, -, hbf, -⟩
  · exact hne ((hok.1.2.1.2.2.1 bl B hB l r hr hl w hw).1 hbk)
  · exact hne ((hok.1.2.1.2.2.2.1 bl B hB c0 p pg hpr hown hpg hfl i hi).1.1 hbf)

/-- **The middle records are well-formed** (see the module doc). -/
theorem wOK_delMid (T : TxView) (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (hok : wOK X1) (hwr : wrFacts X1) (hgens : gensOK T X1) (hR1 : X1.t.bs !! X1.rl = some R1)
    (hn : R1.bm !! n = some c) (hC : X1.t.bs !! c = some C) (hd : objsDisj X1.t)
    (hpx : pagesExt X1.v.pages) :
    wOK (delMid X1 c C R1 n D) := by
  have hcr : c ≠ X1.rl := hwr.2.2 R1 hR1 n c hn
  have hvw : viewWF X1.v := hok.2.2.2.2.2.2.2
  have hokR := wOK_wOKR X1 hok
  have h0R : R1.ib.root' ≠ W64 0 := hok.1.2.1.2.2.2.2 R1 hR1
  have hrt : rtOK X1 X1.rl := rtOK_init X1 X1.rl hok hvw (by rw [hR1]; rfl)
  have h64 : ∀ p pg, X1.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp; have := hpx p pg hp; omega
  -- the cached child's value
  obtain ⟨C', v, hC', hent, -, -, -, -, -, hbo, htk0⟩ := (hok.2.1 X1.rl R1 hR1).2 n c hn
  obtain ⟨we, hwe, hwk, hwv, -⟩ := Spill.entryIn_rootEnts hokR hwr.1 hR1 h0R hrt h64 hent
  have hval : ∀ l r, R1.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws,
      w.key = n → w.value = v := by
    intro l r hr hl w hw hk
    have hwA := Spill.mem_allEnts_node hokR hwr.1 hrt hR1 h0R hr hl hw
    have := WOpen.allEnts_key_inj X1 hok X1.rl R1 hR1 w we hwA hwe (by rw [hk, hwk])
    rw [this, hwv]
  -- the root's cache names `c` at `n` only
  have hinj : ∀ k c', R1.bm !! k = some c' → k ≠ n → c' ≠ c := by
    intro k c' hk hkn e
    subst e
    have h1 := hgens.2.1 n c' (by unfold bktLoc; rw [hR1]; exact hn)
    have h2 := hgens.2.1 k c' (by unfold bktLoc; rw [hR1]; exact hk)
    rw [h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact hkn h2.1.symm
  have hback := delMid_back X1 c C R1 n D hcr
  have hYrl : (delMid X1 c C R1 n D).t.bs !! X1.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, if_pos rfl]
  have hYold : ∀ k B, k ≠ c → k ≠ X1.rl → X1.t.bs !! k = some B →
      (delMid X1 c C R1 n D).t.bs !! k = some B := by
    intro k B h1 h2 h3; rw [delMid_bs, if_neg (Ne.symm h1), if_neg h2]; exact h3
  obtain ⟨⟨tw, ⟨tpm, tbuf, tls, tps, trni⟩, t2, t3, trl, tall⟩, hkn, hpg, heb, hhs, hlv, hnl, hv⟩ :=
    hok
  refine ⟨⟨tw, ⟨tpm, tbuf, ?_, ?_, ?_⟩, t2, t3, by show ((delMid X1 c C R1 n D).t.bs !! X1.rl).isSome; rw [hYrl]; rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hv⟩
  · -- leafShape
    intro k B hB l r hr hl w hw
    rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
    · exact tls X1.rl R1 hR1 l r hr hl w hw
    · exact tls k B hB0 l r hr hl w hw
  · -- posShape
    intro k B hB c0 p pg hpr hown hp hfl i hi
    rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
    · exact tps X1.rl R1 hR1 c0 p pg hpr hown hp hfl i hi
    · exact tps k B hB0 c0 p pg hpr hown hp hfl i hi
  · -- the root not inline
    intro B hB
    change (delMid X1 c C R1 n D).t.bs !! X1.rl = some B at hB
    rw [hYrl] at hB; cases hB; exact trni R1 hR1
  · -- every bucket clean, its cache's children buckets
    intro k B hB
    rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨hkr, hB0⟩
    · obtain ⟨hcl, -⟩ := tall X1.rl R1 hR1
      refine ⟨bktClean_unopen _ _ _ R1 n hcl fun l r hr hl w hw _ hk => ?_, fun k c' e => ?_⟩
      · rw [hval l r hr hl w hw hk]; exact hbo
      · obtain ⟨hkn', e0⟩ := (GMap.lookup_delete_Some _ _ _ _).1 e
        have hc'c := hinj k c' e0 (Ne.symm hkn')
        by_cases hc'r : c' = X1.rl
        · rw [hc'r, hYrl]; rfl
        · obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 ((tall X1.rl R1 hR1).2 k c' e0)
          rw [hYold c' B' hc'c hc'r hB']; rfl
    · obtain ⟨hcl, -⟩ := tall k B hB0
      exact ⟨hcl, fun k' c' e => (bm_nonroot X1 ⟨⟨tw, ⟨tpm, tbuf, tls, tps, trni⟩, t2, t3, trl, tall⟩,
        hkn, hpg, heb, hhs, hlv, hnl, hv⟩ k B hB0 hkr k' c' e).elim⟩
  · -- keys and nested buckets
    intro k B hB
    rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨hkr, hB0⟩
    · obtain ⟨hkk, hnest⟩ := hkn X1.rl R1 hR1
      refine ⟨bktKeys_unopen _ R1 n hkk fun l r hr hl w hw _ hk hroot => ?_, fun k c' e => ?_⟩
      · rw [hval l r hr hl w hw hk] at hroot ⊢; exact htk0 hroot
      · obtain ⟨hkn', e0⟩ := (GMap.lookup_delete_Some _ _ _ _).1 e
        have hc'c := hinj k c' e0 (Ne.symm hkn')
        have hc'r : c' ≠ X1.rl := hwr.2.2 R1 hR1 k c' e0
        obtain ⟨C0, v0, hC0, hin, h16, hinl, hr0, hrn0, hip0, hbo0, htk⟩ := hnest k c' e0
        exact ⟨C0, v0, hYold c' C0 hc'c hc'r hC0, hin, h16, hinl, hr0, hrn0, hip0, hbo0, htk⟩
    · obtain ⟨hkk, -⟩ := hkn k B hB0
      exact ⟨hkk, fun k' c' e => (bm_nonroot X1 ⟨⟨tw, ⟨tpm, tbuf, tls, tps, trni⟩, t2, t3, trl, tall⟩,
        hkn, hpg, heb, hhs, hlv, hnl, hv⟩ k B hB0 hkr k' c' e).elim⟩
  · -- nodes' pages
    intro k B hB l r hr
    rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
    · exact hpg X1.rl R1 hR1 l r hr
    · exact hpg k B hB0 l r hr
  · -- entries bounded
    intro k B hB l r hr
    rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
    · exact heb X1.rl R1 hR1 l r hr
    · exact heb k B hB0 l r hr
  · -- handles
    intro b nm hb
    obtain ⟨B0, hB0⟩ := Option.isSome_iff_exists.1 (hhs b nm hb)
    show ((delMid X1 c C R1 n D).t.bs ∪ (delMid X1 c C R1 n D).t.deadB) !! b |>.isSome
    rw [GMap.lookup_union, delMid_deadB]
    by_cases hbc : c = b
    · rw [if_pos hbc]; cases (delMid X1 c C R1 n D).t.bs !! b <;> rfl
    · rw [if_neg hbc]
      unfold WTx.bobjs at hB0
      rw [GMap.lookup_union] at hB0
      cases hx : X1.t.bs !! b with
      | some B =>
        by_cases hbr : b = X1.rl
        · subst hbr; rw [hYrl]; rfl
        · rw [hYold b B (Ne.symm hbc) hbr hx]; rfl
      | none =>
        rw [hx] at hB0
        simp only [Option.none_or] at hB0
        rw [hB0]; cases (delMid X1 c C R1 n D).t.bs !! b <;> rfl
  · -- live sets
    obtain ⟨l1, l2, l3, l4, l5⟩ := hlv
    have hobjs : (delMid X1 c C R1 n D).t.objs = X1.t.objs := by
      show ((X1.setBkt X1.rl (bUnopen R1 n)).killBkt c C).t.objs = X1.t.objs
      have hd2 : objsDisj (X1.setBkt X1.rl (bUnopen R1 n)).t :=
        WOpen.objsDisj_setBkt' X1 X1.rl R1 (bUnopen R1 n) hd hR1
      have hC2 : (X1.setBkt X1.rl (bUnopen R1 n)).t.bs !! c = some C := by
        show (X1.t.bs.insert X1.rl _) !! c = _
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hcr)]; exact hC
      rw [objs_killBkt _ c C hd2 hC2]
      exact WOpen.objs_setBkt' X1 X1.rl R1 (bUnopen R1 n) hd hR1
    refine ⟨(delMid_liveB X1 c C R1 n D X1.rl).2 ⟨Ne.symm hcr, l1⟩, fun l hl => ?_,
      fun k B hB => ?_, fun k B l r hB hr => ?_, fun l hl => ?_⟩
    · rw [hobjs]; exact l2 l ((delMid_live X1 c C R1 n D l).1 hl).1
    · refine (delMid_liveB X1 c C R1 n D k).2 ⟨(hback k B hB).1, ?_⟩
      rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
      · exact l1
      · exact l3 k B hB0
    · have hkc := (hback k B hB).1
      obtain ⟨B0, hB0, hns⟩ : ∃ B0, X1.t.bs !! k = some B0 ∧ B.ns = B0.ns := by
        rcases (hback k B hB).2 with ⟨rfl, rfl⟩ | ⟨-, hB0⟩
        · exact ⟨R1, hR1, rfl⟩
        · exact ⟨B, hB0, rfl⟩
      rw [hns] at hr
      refine (delMid_live X1 c C R1 n D l).2 ⟨l4 k B0 l r hB0 hr, ?_⟩
      exact hd k B0 hB0 l (by rw [hr]; rfl) c C hC (Ne.symm hkc)
    · intro hl'
      obtain ⟨hl1, hl2⟩ := (delMid_live X1 c C R1 n D l).1 hl'
      show False
      have hdl : ((C.ns.fmap fun r => (c, r)) ∪ X1.t.dead) !! l |>.isSome := hl
      rw [GMap.lookup_union, GMap.lookup_fmap, hl2] at hdl
      simp only [Option.map_none, Option.none_or] at hdl
      exact l5 l hdl hl1
  · -- the node registry
    intro m b p hm hl
    obtain ⟨hl1, hl2⟩ := (delMid_live X1 c C R1 n D m).1 hl
    obtain ⟨B0, r, hB0, hr, hp⟩ := hnl m b p hm hl1
    by_cases hbc : b = c
    · subst hbc; rw [hC] at hB0; cases hB0; rw [hl2] at hr; cases hr
    · by_cases hbr : b = X1.rl
      · subst hbr; rw [hR1] at hB0; cases hB0
        exact ⟨bUnopen R1 n, r, hYrl, hr, hp⟩
      · exact ⟨B0, r, hYold b B0 hbc hbr hB0, hr, hp⟩

end wok

end Write

end bbolt
end EtcdGrove
end Perennial
