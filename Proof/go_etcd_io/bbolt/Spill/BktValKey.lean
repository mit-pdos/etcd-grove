/-
`Bucket.spill` (U9p, `notes/bbolt-proof-plan.md`): **a cached child without a root node, at its
entry** (`bvalS_cachedEntry`). The root spill's loop leaves such a child's entry in the root's
leaf as it is; the root's `InitB.sb` needs its value a `bvalS`. `bktNested` names the child's
value `v` (`entryIn`: in a leaf node, or on a view leaf page under a page position) and its
header; the bucket's keys being distinct (`allEnts_key_injR`, `Read/WOpenWOK.allEnts_key_inj`'s
proof under `wOKR`: it uses only `bktClean`, the keys and the view) and both entries the bucket's
(`mem_allEnts_node`, `mem_allEnts_page`: their positions are the walk's), the entry's value is `v`,
a `bvalS` (`bvalS_cachedNil`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktVal
public import Proof.go_etcd_io.bbolt.Spill.BktSlotCov
public import Proof.go_etcd_io.bbolt.Read.LeafOfT
public import Proof.go_etcd_io.bbolt.Write.DataWalk

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write

namespace Spill

section key
variable [GooseExts]

omit [GooseExts] in
theorem wsAt_of_memR : ∀ (ws : List WEntry), Write.wsPw ws → ∀ w ∈ ws, ws[wsIdx ws w.key]? = some w
  | [], _, w, hw => by cases hw
  | a :: t, hs, w, hw => by
    rw [Write.wsPw, List.pairwise_cons] at hs
    rcases List.mem_cons.1 hw with rfl | hw'
    · unfold wsIdx
      rw [List.takeWhile_cons_of_neg (by simpa using go.goStringLt_irrefl w.key)]
      rfl
    · have ih := wsAt_of_memR t hs.2 w hw'
      have hlt := hs.1 w hw'
      unfold wsIdx at ih ⊢
      rw [List.takeWhile_cons_of_pos (by simpa using hlt), List.length_cons]
      simpa using ih

/-- A leaf of a well-formed writer's logical tree is sorted. -/
theorem leaf_pwR (X : WX) (hok : wOKR X) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B)
    (p : w64) (ws : List WEntry) (hL : ltree X bl p = some (true, ws)) : wsPw ws := by
  have hc : bktClean X.v X.t.mv.pgid'.toNat bl B := (hok.1.2.2.2.2.2 bl B hB).1
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

/-- **Two entries of one key in a well-formed bucket are one** (`wOKR`; `allEnts_key_inj`'s proof). -/
theorem allEnts_key_injR (X : WX) (hok : wOKR X) (k : Loc) (R : BRec) (hR : X.t.bs !! k = some R)
    (w1 w2 : WEntry) (h1 : w1 ∈ X.allEnts k) (h2 : w2 ∈ X.allEnts k) (hk : w1.key = w2.key) :
    w1 = w2 := by
  have hc : bktClean X.v X.t.mv.pgid'.toNat k R := (hok.1.2.2.2.2.2 k R hR).1
  obtain ⟨bnd, hbk⟩ := (hok.2.1 k R hR).1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hwalk := LR.bInvL_walk X k R bnd _ hR hc hbk hv X.fuel _ _
    (LR.bInvL_root X k R bnd _ hR hc hbk hv)
  have hall : X.allEnts k =
      ((Write.lleavesB (ltree X) k X.fuel (X.rootPid k) (none, none)).map fun x => x.2.2).flatten := by
    unfold WX.allEnts WX.leaves; rw [Write.lleavesB_snd]
  rw [hall, List.mem_flatten] at h1 h2
  obtain ⟨l1, hl1, hw1⟩ := h1
  obtain ⟨x1, hx1, rfl⟩ := List.mem_map.1 hl1
  obtain ⟨l2, hl2, hw2⟩ := h2
  obtain ⟨x2, hx2, rfl⟩ := List.mem_map.1 hl2
  have hk1 := hwalk.1 x1 hx1 w1 hw1
  have hk2 := hwalk.1 x2 hx2 w2 hw2
  have hxy : x1 = x2 := by
    apply Classical.byContradiction
    intro hne
    have := LR.pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hwalk.2.1 x1 hx1 x2 hx2 hne
    exact this w1.key hk1 (hk ▸ hk2)
  subst hxy
  have hL := Write.lleavesB_leaf (ltree X) k X.fuel _ _ x1 hx1
  have hs := leaf_pwR X hok k R hR x1.1 x1.2.2 hL
  have e1 := wsAt_of_memR x1.2.2 hs w1 hw1
  have e2 := wsAt_of_memR x1.2.2 hs w2 hw2
  rw [hk, e2] at e1
  exact (Option.some.inj e1).symm

/-! ## The leaves of the walk -/

mutual
theorem lvs_of_pos (L : LTree) (bl : Loc) : ∀ (t : RTree) (p : w64) (ws : List WEntry),
    ltIs L bl t → p ∈ t.pos → L bl p = some (true, ws) → ws ∈ t.lvs
  | .mk q true ws' cs, p, ws, h, hp, hL => by
    simp only [ltIs] at h
    simp only [RTree.pos, List.mem_singleton] at hp
    subst hp
    rw [h.1] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hL
    subst hL
    simp [RTree.lvs]
  | .mk q false ws' cs, p, ws, h, hp, hL => by
    simp only [ltIs] at h
    simp only [RTree.pos, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rw [h.1] at hL; simp at hL
    · simp only [RTree.lvs]
      exact lvsL_of_pos L bl ws' cs p ws h.2 hp hL
theorem lvsL_of_pos (L : LTree) (bl : Loc) : ∀ (ws' : List WEntry) (cs : List RTree) (p : w64)
    (ws : List WEntry), ltIsL L bl ws' cs → p ∈ RTree.posL cs → L bl p = some (true, ws) →
    ws ∈ RTree.lvsL cs
  | [], [], _, _, _, hp, _ => by simp [RTree.posL] at hp
  | w :: ws', t :: ts, p, ws, h, hp, hL => by
    simp only [ltIsL] at h
    simp only [RTree.posL, List.mem_append] at hp
    simp only [RTree.lvsL, List.mem_append]
    rcases hp with hp | hp
    · exact Or.inl (lvs_of_pos L bl t p ws h.2.1 hp hL)
    · exact Or.inr (lvsL_of_pos L bl ws' ts p ws h.2.2 hp hL)
  | [], _ :: _, _, _, h, _, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, _, h, _, _ => by simp only [ltIsL] at h
end

/-- A leaf position's entries are the bucket's. -/
theorem mem_allEnts_pos {X : WX} {bl : Loc} (hrt : rtOK X bl) {p : w64}
    (hp : p ∈ X.positions bl) {ws : List WEntry} (hL : ltree X bl p = some (true, ws)) {w : WEntry}
    (hw : w ∈ ws) : w ∈ X.allEnts bl := by
  obtain ⟨t, ht, htp, hth, -⟩ := hrt
  rw [positions_rt X bl t ht htp hth] at hp
  unfold WX.allEnts WX.leaves
  rw [← htp, lleaves_ltIs (ltree X) bl t X.fuel ht hth]
  exact List.mem_flatten.2 ⟨ws, lvs_of_pos _ _ t p ws ht hp hL, hw⟩

/-- **A leaf node's entries are the bucket's** (a bucket with a root page). -/
theorem mem_allEnts_node {X : WX} (hok : wOKR X) (hreach : liveReach X) {bl : Loc}
    (hrt : rtOK X bl) {B : BRec} (hB : X.t.bs !! bl = some B) (h0 : B.ib.root' ≠ W64 0)
    {l : Loc} {r : NRec} (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = true) {w : WEntry}
    (hw : w ∈ r.ws) : w ∈ X.allEnts bl := by
  have hcl : bktClean X.v X.t.mv.pgid'.toNat bl B := (hok.1.2.2.2.2.2 bl B hB).1
  obtain ⟨bnd, hbk⟩ := (hok.2.1 bl B hB).1
  have hlive := wOKR_nsLive X hok bl B l r hB hr
  obtain ⟨rt, hrtI, hd⟩ := hreach.2 bl B l r hB hr hlive
  have hpos := node_pos X bl B hB hcl hbk.2.1 hrt h0 rt l hrtI hd r hr
  have hL := ltree_node_rbl X bl B hB hcl h0 l r hr
  rw [hl] at hL
  exact mem_allEnts_pos hrt hpos hL hw

theorem treeHas_of_ownHas {P : Pages} {a x : Nat} (h : ownHas P a x) : treeHas P a x := by
  induction h with
  | root _ pg hpg => exact treeHas.root _ pg hpg
  | child a pg i x hpa hfl hi _ ih => exact treeHas_child hpa hfl hi ih

/-- **A view leaf page's entries under a page position are the bucket's.** -/
theorem mem_allEnts_page {X : WX} (hok : wOKR X) (hreach : liveReach X) {bl : Loc}
    (hrt : rtOK X bl) {B : BRec} (hB : X.t.bs !! bl = some B)
    (h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64) {c0 p : Nat} {pg : List w8} {i : Nat}
    (hpr : posRoot B c0) (hown : ownHas X.v.pages c0 p) (hpg : X.v.pages !! p = some pg)
    (hfl : pageFlags pg = leafPageFlag) (hi : i < pageCount pg) :
    pageW pg i ∈ X.allEnts bl := by
  have hcl : bktClean X.v X.t.mv.pgid'.toNat bl B := (hok.1.2.2.2.2.2 bl B hB).1
  obtain ⟨bnd, hbk⟩ := (hok.2.1 bl B hB).1
  have hrt' := hrt
  obtain ⟨t, ht, htp, hth, -⟩ := hrt'
  have hposeq := positions_rt X bl t ht htp hth
  -- the position at `c0`
  have hq : B.ib.root' ≠ W64 0 ∧ W64 (c0 : Int) ∈ t.pos ∧
      ∀ d, treeHas X.v.pages c0 d → B.nm !! W64 (d : Int) = none := by
    rcases hpr with ⟨hrn, h0, rfl⟩ | ⟨l, k, hpp, hlt⟩
    · refine ⟨h0, ?_, fun d _ => by rw [(hcl.2.2.1 hrn).2]; rfl⟩
      rw [w64_toNat_cast]
      have : t.pid = B.ib.root' := by rw [htp]; simp [WX.rootPid, hB]
      rw [← this, pos_eq _ _ t ht]
      exact List.mem_cons_self
    · obtain ⟨rl', w, hrl, hlf, hw, hwq, hnm⟩ := hpp
      have h0 : B.ib.root' ≠ W64 0 := by
        intro e; have := hcl.2.2.2.2.2.2.1 e l rl' hrl; rw [hlf] at this; cases this
      have hlive := wOKR_nsLive X hok bl B l rl' hB hrl
      obtain ⟨rt, hrtI, hd⟩ := hreach.2 bl B l rl' hB hrl hlive
      have hpos := node_pos X bl B hB hcl hbk.2.1 hrt h0 rt l hrtI hd rl' hrl
      rw [hposeq] at hpos
      have hL := ltree_node_rbl X bl B hB hcl h0 l rl' hrl
      rw [hlf] at hL
      have hqp := pos_child (ltree X) bl t ht _ hpos rl'.ws hL w (List.mem_of_getElem? hw)
      rw [hwq] at hqp
      refine ⟨h0, hqp, fun d hd => ?_⟩
      have := hcl.2.2.2.2.2.2.2.2.2.1 l k _ ⟨rl', w, hrl, hlf, hw, hwq, hnm⟩ d
      rw [w64_cast_toNat hlt] at this
      exact this hd
  obtain ⟨h0, hqpos, hfree⟩ := hq
  obtain ⟨cpg, hcpg⟩ := ownHas_page hown
  have hfree' : ∀ d, treeHas X.v.pages (W64 (c0 : Int)).toNat d → B.nm !! W64 (d : Int) = none := by
    rw [w64_cast_toNat (h64 c0 cpg hcpg)]; exact hfree
  have hppos := pos_ownHas hB h0 h64 ht hfree' c0 p hown (by
    rw [w64_cast_toNat (h64 c0 cpg hcpg)]; exact treeHas.root c0 cpg hcpg) hqpos
  have hL := ltree_unmat X bl B hB h0 (W64 (p : Int)) (hfree p (treeHas_of_ownHas hown)) pg
    (by rw [w64_cast_toNat (h64 p pg hpg)]; exact hpg)
  have ht' : decide (pageFlags pg = leafPageFlag) = true := by simp [hfl]
  rw [ht'] at hL
  exact mem_allEnts_pos hrt (by rw [hposeq]; exact hppos) hL
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

/-- **A cached child without a root node, at its entry in a leaf node** of a bucket with a root
page: the entry's value is the child's (`bktNested`'s, by the bucket's keys being distinct), so it
is a `bvalS` and the child's header is its. -/
theorem bvalS_cachedEntry {X : WX} {C : CommitSt} (hok : wOKR X) (hreach : liveReach X)
    (hcok : treeOK C) (hcp : X.v.pages = C.pages) (hcm : C.hwm ≤ X.t.mv.pgid'.toNat)
    {hwm : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg)
    {bl : Loc} (hrt : rtOK X bl) {B : BRec} (hB : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) {l : Loc} {r : NRec} (hr : B.ns !! l = some r)
    (hl : r.nv.isLeaf' = true) {w : WEntry} (hw : w ∈ r.ws) {c : Loc}
    (hk : B.bm !! w.key = some c) {Cc : BRec} (hc : X.t.bs !! c = some Cc)
    (hrn : Cc.bv.rootNode' = null) :
    Cc.ib = ibOf w.value ∧ ∃ S, bvalS P hwm w.value S ∧
      ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages w.value s := by
  have h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp
    have := hcok.2.2.2.1 p pg (by rw [← hcp]; exact hp)
    have := X.t.mv.pgid'.isLt
    omega
  obtain ⟨v, S, hent, hib, hS, hsl⟩ := bvalS_cachedNil hok hcok hcp hch hag hB hk hc hrn
  have hwA := mem_allEnts_node hok hreach hrt hB h0 hr hl hw
  have hv : w.value = v := by
    rcases hent with ⟨l', r', w', hr', hl', hw', hkey, -, hval⟩ |
      ⟨c0, p, pg, i, hpr, hown, hpg, hfl, hi, hkey, -, hval⟩
    · have := allEnts_key_injR X hok bl B hB w w' hwA
        (mem_allEnts_node hok hreach hrt hB h0 hr' hl' hw') hkey.symm
      subst this; exact hval
    · have hpA := mem_allEnts_page hok hreach hrt hB h64 hpr hown hpg hfl hi
      have hk' : w.key = (pageW pg i).key := by simp [pageW, hfl, hkey]
      have := allEnts_key_injR X hok bl B hB w _ hwA hpA hk'
      rw [this]; simp [pageW, hfl, hval]
  subst hv
  exact ⟨hib, S, hS, hsl⟩

end key

end Spill

end bbolt
end EtcdGrove
end Perennial
