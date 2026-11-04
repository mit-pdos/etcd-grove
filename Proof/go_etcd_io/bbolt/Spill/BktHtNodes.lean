/-
`Bucket.spill`'s initial trees (U9i, `notes/bbolt-proof-plan.md`), part 6: **the heights of a
clean bucket's nodes** (`nodeHts`): from its logical tree's finite tree (`rtOK`: leaves at one
depth, height below the fuel) and its nodes reached from its root node (`descIn`, `liveReach`),
a height function with `InitB`'s `hts` (a leaf `0`, a branch one more than its children, a page
child's height its page's), the root node's below the fuel.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktHt
public import Proof.go_etcd_io.bbolt.Spill.BktInit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section nodes
variable [GooseExts]

variable {X : WX} {bl : Loc} {B : BRec} {C : CommitSt} {pht : Nat → Nat}
  {bnd : Loc → Option (List w8) × Option (List w8)}

/-- The premises of `nodeHts` (`InitB`'s but the heights, and the finite tree). -/
structure HtB (X : WX) (bl : Loc) (B : BRec) (C : CommitSt) (pht : Nat → Nat)
    (bnd : Loc → Option (List w8) × Option (List w8)) : Prop where
  hB : X.t.bs !! bl = some B
  clean : bktClean X.v X.t.mv.pgid'.toNat bl B
  keys : bktKeysB X.v B bnd
  ne2 : ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → 2 ≤ r.ws.length
  cpages : X.v.pages = C.pages
  hpht : pageHts C.pages pht
  rn : B.bv.rootNode' ≠ null
  reach : ∀ l r, B.ns !! l = some r → descIn B B.bv.rootNode' l
  rt : rtOK X bl

theorem HtB.nc (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} (hr : B.ns !! l = some r) :
    nodeClean X.v X.t.mv.pgid'.toNat bl B l r := H.clean.2.2.2.2.2.2.2.1 l r hr

theorem HtB.ltree_node (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} {pid : w64}
    (hr : B.ns !! l = some r) (hres : resolve B pid = some l) :
    ltree X bl pid = some (r.nv.isLeaf', r.ws) := by
  unfold ltree; rw [H.hB]; simp only; rw [hres]; simp only [hr, Option.map_some]

theorem HtB.root_ne (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = false) : B.ib.root' ≠ W64 0 := by
  intro h0
  have := H.clean.2.2.2.2.2.2.1 h0 l r hr
  rw [hl] at this; cases this

theorem HtB.ltree_pages (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} {i : Nat}
    {w : WEntry} (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = false) (hw : r.ws[i]? = some w)
    (hnm : B.nm !! w.pgid = none) :
    ∀ q : w64, treeHas C.pages w.pgid.toNat q.toNat →
      ltree X bl q = (C.pages !! q.toNat).map pgRead := by
  intro q hq
  have h0 := H.root_ne hr hl
  have hpos : pagePosAt B l i w.pgid := ⟨r, w, hr, hl, hw, rfl, hnm⟩
  have hq' : treeHas X.v.pages w.pgid.toNat q.toNat := by rw [H.cpages]; exact hq
  have hfree := H.clean.2.2.2.2.2.2.2.2.2 l i w.pgid hpos q.toNat hq'
  rw [show W64 (q.toNat : Int) = q by simp] at hfree
  unfold ltree; rw [H.hB]; simp only
  have hres : resolve B q = none := by unfold resolve; rw [if_neg h0]; exact hfree
  rw [hres]; simp only
  unfold wpageAt; rw [if_neg h0, Option.map_map, H.cpages]; rfl

/-- A node with a child is a branch. -/
theorem HtB.branch_of_child (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} {c : Loc}
    (hr : B.ns !! l = some r) (hc : c ∈ r.cs) : r.nv.isLeaf' = false ∧ ∃ rc,
      B.ns !! c = some rc ∧ rc.nv.parent' = l ∧ ∃ (i : Nat) (w : WEntry), r.ws[i]? = some w ∧
        w.pgid = rc.nv.pgid' := by
  obtain ⟨rc, hrc, hpc⟩ := (H.nc hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c hc
  have hl0 : l ≠ null := (H.clean.2.2.2.2.1 _ l (H.nc hr).2.2.2.2.2.2.2.1).1
  have hpn : rc.nv.parent' ≠ null := by rw [hpc]; exact hl0
  obtain ⟨rp, hrp, hpl, -⟩ := (H.nc hrc).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
  rw [hpc, hr] at hrp; cases hrp
  obtain ⟨-, rp, i, w, hrp, hwi, hwp, -⟩ := (H.keys.2.2 c rc hrc).2.2.1 hpn
  rw [hpc, hr] at hrp; cases hrp
  exact ⟨hpl, rc, hrc, hpc, i, w, hwi, hwp⟩

/-- A materialized node's position resolves to it. -/
theorem HtB.resolve_node (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) (h0 : B.ib.root' ≠ W64 0) : resolve B r.nv.pgid' = some l :=
  resolve_nm h0 (H.nc hr).2.2.2.2.2.2.2.1

theorem HtB.t_root (H : HtB X bl B C pht bnd) {t : RTree} (hp : t.pid = X.rootPid bl) :
    resolve B t.pid = some B.bv.rootNode' := by
  have hrp : X.rootPid bl = B.ib.root' := by simp only [WX.rootPid, H.hB, Option.map_some, Option.getD_some]
  rw [hp, hrp]
  unfold resolve
  split
  · rw [if_neg H.rn]
  · exact H.clean.2.2.2.1 H.rn

/-- A child of a node at a position of the finite tree is at one too. -/
theorem HtB.inT_child (H : HtB X bl B C pht bnd) {t : RTree} (ht : ltIs (ltree X) bl t)
    {n c : Loc} {rn : NRec} (hrn : B.ns !! n = some rn) (hc : c ∈ rn.cs) {k : Nat} {s : RTree}
    (hs : subT t k s) (hres : resolve B s.pid = some n) :
    ∃ k s, subT t k s ∧ resolve B s.pid = some c := by
  obtain ⟨hlf, rc, hrc, -, i, w, hwi, hwp⟩ := H.branch_of_child hrn hc
  have hls := subT_ltIs ht hs
  obtain ⟨p, b, ws, cs⟩ := s
  obtain ⟨hL, -, hbr⟩ := ltIs_mk hls
  simp only [RTree.pid] at hres
  rw [H.ltree_node hrn hres] at hL
  simp only [Option.some.injEq, Prod.mk.injEq] at hL
  obtain ⟨hb, hws⟩ := hL
  rw [hlf] at hb; subst hb; subst hws
  have g := ltIsL_get (hbr rfl)
  have hi : i < cs.length := by rw [g.1]; exact (List.getElem?_eq_some_iff.1 hwi).1
  obtain ⟨w', hw', hcp, -⟩ := g.2 i cs[i] (List.getElem?_eq_getElem hi)
  rw [hwi] at hw'; cases hw'
  refine ⟨k + 1, cs[i], subT.child k p rn.ws cs cs[i] hs (List.getElem_mem hi), ?_⟩
  rw [hcp, hwp]
  exact H.resolve_node hrc (H.root_ne hrn hlf)

/-- **Every node is at a position of the finite tree.** -/
theorem HtB.inT (H : HtB X bl B C pht bnd) {t : RTree} (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) {l : Loc} (hd : descIn B B.bv.rootNode' l) :
    ∃ k s, subT t k s ∧ resolve B s.pid = some l := by
  have key : ∀ a d, descIn B a d → (∃ k s, subT t k s ∧ resolve B s.pid = some a) →
      ∃ k s, subT t k s ∧ resolve B s.pid = some d := by
    intro a d h
    induction h with
    | self => exact id
    | child n c d rn hrn hc _ ih =>
      rintro ⟨k, s, hs, hres⟩
      exact ih (H.inT_child ht hrn hc hs hres)
  exact key _ _ hd ⟨0, t, subT.refl, H.t_root hp⟩

/-- A child's page subtree: its tree's height is its page's, and it has children at every
branch. -/
theorem HtB.pageChild (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} {i : Nat} {w : WEntry}
    (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = false) (hw : r.ws[i]? = some w)
    (hnm : B.nm !! w.pgid = none) {c : RTree} (hc : ltIs (ltree X) bl c) (hcp : c.pid = w.pgid) :
    c.ht = pht w.pgid.toNat ∧ neT c := by
  have hwf : treeWF C.pages X.t.mv.pgid'.toNat c.pid.toNat := by
    rw [hcp, ← H.cpages]
    exact ((H.nc hr).2.2.2.2.2.2.2.2.2.2.2.2.1 hl).2.2 w (List.mem_of_getElem? hw) |>.2.2 hnm
  have := pageT (ltree X) bl C.pages X.t.mv.pgid'.toNat pht H.hpht _ c (Nat.lt_succ_self _) hc hwf
    (by rw [hcp]; exact H.ltree_pages hr hl hw hnm)
  rw [hcp] at this; exact this

/-- **A node's tree has children at every branch.** -/
theorem HtB.neT_node (H : HtB X bl B C pht bnd) : ∀ n (s : RTree), s.ht < n →
    ltIs (ltree X) bl s → ∀ l r, B.ns !! l = some r → resolve B s.pid = some l → neT s
  | 0, _, h, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, .mk p b ws cs, hn, hls, l, r, hr, hres => by
    simp only [RTree.pid] at hres
    obtain ⟨hL, hlf, hbr⟩ := ltIs_mk hls
    rw [H.ltree_node hr hres] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hb, hws⟩ := hL
    subst hb; subst hws
    cases hleaf : r.nv.isLeaf' with
    | true =>
      have hcs := hlf hleaf
      intro k q b' ws' cs' hs
      rcases subT_cases hs with ⟨-, e⟩ | ⟨c, hc, -⟩
      · cases e; exact ⟨fun _ => hcs, (fun e => by cases e)⟩
      · rw [hcs] at hc; cases hc
    | false =>
      have g := ltIsL_get (hbr hleaf)
      have h2 := H.ne2 l r hr hleaf
      have hcs : cs ≠ [] := by intro e; have := g.1; rw [e] at this; simp at this; omega
      have hc : ∀ c ∈ cs, neT c := by
        intro c hcm
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcm
        obtain ⟨w, hw, hcp, hcl⟩ := g.2 i cs[i] (List.getElem?_eq_getElem hi)
        have hlt : cs[i].ht < n := by
          have := htL_ge hcm; simp only [RTree.ht] at hn; omega
        cases hnm : B.nm !! w.pgid with
        | some c =>
          obtain ⟨rc, hrc, -⟩ := (H.clean.2.2.2.2.1 _ c hnm).2
          exact H.neT_node n cs[i] hlt hcl c rc hrc
            (by rw [hcp]; exact resolve_nm (H.root_ne hr hleaf) hnm)
        | none => exact (H.pageChild hr hleaf hw hnm hcl hcp).2
      intro k q b' ws' cs' hs
      rcases subT_cases hs with ⟨-, e⟩ | ⟨c, hcm, k', -, hs'⟩
      · cases e; exact ⟨(fun e => by cases e), fun _ => hcs⟩
      · exact hc c hcm k' q b' ws' cs' hs'

open Classical in
/-- The height of node `l`: its tree's at the finite tree's position resolving to it. -/
def htOf (t : RTree) (B : BRec) (l : Loc) : Nat :=
  if h : ∃ k s, subT t k s ∧ resolve B s.pid = some l then
    (Classical.choose (Classical.choose_spec h)).ht else 0

theorem HtB.htOf_eq (H : HtB X bl B C pht bnd) {t : RTree} (ht : ltIs (ltree X) bl t)
    {k : Nat} {s : RTree} {l : Loc} (hs : subT t k s) (hres : resolve B s.pid = some l) :
    htOf t B l = s.ht := by
  have hex : ∃ k s, subT t k s ∧ resolve B s.pid = some l := ⟨k, s, hs, hres⟩
  unfold htOf; rw [dif_pos hex]
  obtain ⟨hs', hres'⟩ := Classical.choose_spec (Classical.choose_spec hex)
  generalize Classical.choose (Classical.choose_spec hex) = s' at hs' hres' ⊢
  have hl1 := subT_ltIs ht hs
  have hl2 := subT_ltIs ht hs'
  by_cases h0 : B.ib.root' = W64 0
  · -- an inline bucket: every node a leaf, both trees leaves
    have hleaf : ∀ s : RTree, ltIs (ltree X) bl s → resolve B s.pid = some l → s.ht = 0 := by
      intro s hls hr
      obtain ⟨p, b, ws, cs⟩ := s
      obtain ⟨hL, hlf, -⟩ := ltIs_mk hls
      have hB : (B.ns !! l).isSome := by
        unfold resolve at hr; rw [if_pos h0] at hr
        split at hr
        · cases hr
        · cases hr; obtain ⟨r, hr', -⟩ := (H.clean.2.2.2.2.1 _ _ (H.clean.2.2.2.1 ‹_›)).2
          simp [hr']
      obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 hB
      simp only [RTree.pid] at hr
      rw [H.ltree_node hr' hr] at hL
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      have := H.clean.2.2.2.2.2.2.1 h0 l r hr'
      rw [← hL.1, this] at hlf
      rw [hlf rfl]; rfl
    rw [hleaf s hl1 hres, hleaf s' hl2 hres']
  · have e1 : B.nm !! s.pid = some l := by unfold resolve at hres; rwa [if_neg h0] at hres
    have e2 : B.nm !! s'.pid = some l := by unfold resolve at hres'; rwa [if_neg h0] at hres'
    obtain ⟨r1, hr1, hp1⟩ := (H.clean.2.2.2.2.1 _ _ e1).2
    obtain ⟨r2, hr2, hp2⟩ := (H.clean.2.2.2.2.1 _ _ e2).2
    rw [hr1] at hr2; cases hr2
    rw [ltIs_unique _ s' s (Nat.lt_succ_self _) hl2 hl1 (by rw [← hp1, hp2])]

/-- **The heights of a clean bucket's nodes** (see the module doc). -/
theorem HtB.nodeHts (H : HtB X bl B C pht bnd) :
    ∃ ht : Loc → Nat, (∀ l r, B.ns !! l = some r → (r.nv.isLeaf' = true → ht l = 0) ∧
      (r.nv.isLeaf' = false → ∀ w ∈ r.ws, (∀ c, B.nm !! w.pgid = some c → ht c + 1 = ht l) ∧
        (B.nm !! w.pgid = none → pht w.pgid.toNat + 1 = ht l))) ∧
      ht B.bv.rootNode' < X.fuel := by
  obtain ⟨t, hlt, hp, hfuel, D, hD⟩ := H.rt
  obtain ⟨r0, hr0⟩ : ∃ r0, B.ns !! B.bv.rootNode' = some r0 := by
    obtain ⟨r, hr, -⟩ := (H.clean.2.2.2.2.1 _ _ (H.clean.2.2.2.1 H.rn)).2; exact ⟨r, hr⟩
  have hneT : neT t := H.neT_node _ t (Nat.lt_succ_self _) hlt _ r0 hr0 (H.t_root hp)
  refine ⟨htOf t B, ?_, by rw [H.htOf_eq hlt subT.refl (H.t_root hp)]; exact hfuel⟩
  intro l r hr
  obtain ⟨k, s, hs, hres⟩ := H.inT hlt hp (H.reach l r hr)
  rw [H.htOf_eq hlt hs hres]
  have hls := subT_ltIs hlt hs
  obtain ⟨p, b, ws, cs⟩ := s
  obtain ⟨hL, hlf, hbr⟩ := ltIs_mk hls
  simp only [RTree.pid] at hres
  rw [H.ltree_node hr hres] at hL
  simp only [Option.some.injEq, Prod.mk.injEq] at hL
  obtain ⟨hb, hws⟩ := hL
  subst hb; subst hws
  refine ⟨fun hleaf => by rw [hlf hleaf]; rfl, fun hleaf w hw => ?_⟩
  rw [hleaf] at hbr hs
  have g := ltIsL_get (hbr rfl)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hi' : i < cs.length := by rw [g.1]; exact hi
  obtain ⟨w', hw', hcp, hcl⟩ := g.2 i cs[i] (List.getElem?_eq_getElem hi')
  rw [List.getElem?_eq_getElem hi] at hw'; cases hw'
  have hch := child_ht hD hneT hs (List.getElem_mem hi')
  refine ⟨fun c hc => ?_, fun hnm => ?_⟩
  · rw [H.htOf_eq hlt (subT.child k p r.ws cs cs[i] hs (List.getElem_mem hi'))
      (by rw [hcp]; exact resolve_nm (H.root_ne hr hleaf) hc)]
    rw [hleaf]; exact hch
  · rw [← (H.pageChild hr hleaf (List.getElem?_eq_getElem hi) hnm hcl hcp).1]
    rw [hleaf]; exact hch

end nodes

end Spill

end bbolt
end EtcdGrove
end Perennial
