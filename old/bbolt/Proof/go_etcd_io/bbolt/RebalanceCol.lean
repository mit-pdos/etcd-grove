/-
A root collapsed by `node.rebalance` (a branch root `nl` with one child `lc`): the root takes
the child's kind, entries and children (`n.inodes = child.inodes[:]`, `n.children =
child.children`), the child's materialized children are reparented to it, the child is dropped
(`delete(b.nodes, child.pgid)`, its page freed). The bucket `colBkt` stays clean, keeps its keys
(the root's bounds the child's), its parent pointers without cycle, its heights, the nested
buckets' entries, and the tokens but the child's page's.
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceMg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The root after the collapse (its inodes slice `sI`). -/
def colRoot (rn rc : NRec) (sI : GoSlice) : NRec :=
  ⟨{ rn.nv with isLeaf' := rc.nv.isLeaf', inodes' := sI, children' := rc.nv.children' }, rc.ins, rc.ws,
    rc.cs, rn.key, rn.ksrc⟩

/-- The bucket after the collapse of the root `nl` into its child `lc` (page `pgid`). -/
def colBkt (B : BRec) (nl lc : Loc) (pgid : w64) (rn' : NRec) : BRec :=
  { B with nm := GMap.delete pgid B.nm, ns := <[nl := rn']> (reparent (GMap.delete lc B.ns) lc nl) }

theorem col_ns (B : BRec) (nl lc : Loc) (pgid : w64) (rn' : NRec) (y : Loc) :
    (colBkt B nl lc pgid rn').ns !! y =
      if y = nl then some rn' else if y = lc then none else
        (B.ns !! y).map
          (fun x => if x.nv.parent' = lc then { x with nv := { x.nv with parent' := nl } } else x) := by
  show (<[nl := rn']> (reparent (GMap.delete lc B.ns) lc nl)) !! y = _
  rw [rf_lookup, reparent_lookup]
  split
  · rfl
  · by_cases h : y = lc
    · subst h; rw [if_pos rfl, GMap.lookup_delete]; rfl
    · rw [if_neg h, GMap.lookup_delete_ne _ (Ne.symm h)]

theorem col_nm (B : BRec) (nl lc : Loc) (pgid : w64) (rn' : NRec) (k : w64) :
    (colBkt B nl lc pgid rn').nm !! k = if k = pgid then none else B.nm !! k := by
  show (GMap.delete pgid B.nm) !! k = _
  split
  · rename_i h; subst h; rw [GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ (Ne.symm ‹_›)]

section col
variable (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (nl : Loc) (rn : NRec) (w0 : WEntry)
  (lc : Loc) (rc : NRec)
  (hc : bktClean W hwm bl B) (ha : rblAcyc B) (hrn : B.ns !! nl = some rn)
  (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null) (hws : rn.ws = [w0])
  (hlc : B.nm !! w0.pgid = some lc) (hrc : B.ns !! lc = some rc)
include hc ha hrn hbr hpn hws hlc hrc

theorem col_basic :
    rc.nv.parent' = nl ∧ lc ≠ nl ∧ rc.nv.pgid' = w0.pgid ∧ B.nm !! rn.nv.pgid' = some nl ∧
      rn.nv.pgid' ≠ rc.nv.pgid' ∧ B.ib.root' ≠ W64 0 ∧
      (∀ y ry, B.ns !! y = some ry → ry.nv.parent' = nl → y = lc) ∧
      (∀ y ry (j : Nat) (x : WEntry), B.ns !! y = some ry → ry.nv.isLeaf' = false → ry.ws[j]? = some x →
        x.pgid = rc.nv.pgid' → y = nl) ∧
      (∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ y ∨ ry.nv.parent' = null) := by
  have hnn := hc.2.2.2.2.2.2.2.1 nl rn hrn
  obtain ⟨-, -, hkids⟩ := hnn.2.2.2.2.2.2.2.2.2.2.2.1 hbr
  obtain ⟨r1, hr1, hp1⟩ := (hkids w0 (by rw [hws]; exact List.mem_singleton_self _)).2.1 lc hlc
  rw [hrc] at hr1; cases hr1
  obtain ⟨-, r3, hr3, hp3⟩ := hc.2.2.2.2.1 _ _ hlc
  rw [hrc] at hr3; cases hr3
  have hlcn : lc ≠ nl := by
    intro he; subst he; rw [hrn] at hrc; cases hrc; rw [hpn] at hp1
    exact (hc.2.2.2.2.1 _ _ hlc).1 hp1.symm
  have hnm1 := hnn.2.2.2.2.2.2.1
  have hpg : rn.nv.pgid' ≠ rc.nv.pgid' := by
    intro he; rw [he] at hnm1; rw [hp3] at hnm1; exact hlcn (Option.some.inj (hlc.symm.trans hnm1))
  have hroot0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 nl rn hrn; rw [hbr] at this; cases this
  refine ⟨hp1, hlcn, hp3, hnm1, hpg, hroot0, fun y ry hy hp => ?_, fun y ry j x hy hb hj hx => ?_,
    fun y ry hy => ?_⟩
  · obtain ⟨rq, hrq, -, -, x, hx, hxp⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [hp]; exact (hc.2.2.2.2.1 _ _ hnm1).1)
    rw [hp, hrn] at hrq; cases hrq
    rw [hws, List.mem_singleton] at hx; subst hx
    have := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.1
    rw [← hxp, hlc] at this; exact (Option.some.inj this).symm
  · obtain ⟨-, -, hk⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.1 hb
    obtain ⟨r2, hr2, hp2⟩ := (hk x (List.mem_of_getElem? hj)).2.1 lc (by rw [hx, hp3]; exact hlc)
    rw [hrc] at hr2; cases hr2; rw [hp1] at hp2; exact hp2.symm
  · obtain ⟨ht, hh⟩ := ha
    by_cases h : ry.nv.parent' = null
    · exact Or.inr h
    · left; intro he; have := hh y ry hy h; rw [he] at this; omega

theorem col_other (sI : GoSlice) (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hyn : y ≠ nl)
    (hyc : y ≠ lc) :
    (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y =
      some (if ry.nv.parent' = lc then { ry with nv := { ry.nv with parent' := nl } } else ry) := by
  rw [col_ns, if_neg hyn, if_neg hyc, hy]; rfl

theorem col_look (sI : GoSlice) (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hyc : y ≠ lc) :
    ∃ ry', (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y = some ry' ∧
      ry'.nv.pgid' = ry.nv.pgid' ∧ ry'.nv.parent' = (if ry.nv.parent' = lc then nl else ry.nv.parent') := by
  obtain ⟨hp1, hlcn, -⟩ := col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  by_cases hyn : y = nl
  · subst y; rw [hrn] at hy; cases hy
    refine ⟨colRoot rn rc sI, by rw [col_ns, if_pos rfl], rfl, ?_⟩
    show rn.nv.parent' = (if rn.nv.parent' = lc then nl else rn.nv.parent')
    rw [if_neg (by rw [hpn]; intro h; rw [← h] at hlc; exact (hc.2.2.2.2.1 _ _ hlc).1 rfl)]
  rw [col_other W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI y ry hy hyn hyc]
  refine ⟨_, rfl, ?_, ?_⟩ <;> split <;> rfl

/-- Where a page position of the collapsed bucket was. -/
theorem col_pos (sI : GoSlice) (y : Loc) (j : Nat) (c : w64)
    (hp : pagePosAt (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) y j c) :
    y ≠ lc ∧ pagePosAt B (if y = nl then lc else y) j c := by
  obtain ⟨hp1, hlcn, hpg3, hnm1, hpg, hroot0, hkid, honly, -⟩ :=
    col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  obtain ⟨ry', x, hy, hb, hx, hxc, hn⟩ := hp
  rw [col_nm] at hn
  rw [col_ns] at hy
  split at hy
  · rename_i hyn; cases hy; subst y
    have hcn : c ≠ rc.nv.pgid' := by
      intro he; rw [if_pos he] at hn
      exact (honly lc rc j x hrc hb hx (by rw [hxc, he])) ▸ hlcn |> fun h => h rfl
    rw [if_neg hcn] at hn
    exact ⟨Ne.symm hlcn, by rw [if_pos rfl]; exact ⟨rc, x, hrc, hb, hx, hxc, hn⟩⟩
  split at hy
  · cases hy
  rename_i hyn hyc
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hb' : ry.nv.isLeaf' = false := by split at hb <;> exact hb
  have hx' : ry.ws[j]? = some x := by split at hx <;> exact hx
  have hcn : c ≠ rc.nv.pgid' := by
    intro he; exact hyn (honly y ry j x hry hb' hx' (by rw [hxc, he]))
  rw [if_neg hcn] at hn
  exact ⟨hyc, by rw [if_neg hyn]; exact ⟨ry, x, hry, hb', hx', hxc, hn⟩⟩

theorem col_clean (sI : GoSlice) :
    bktClean W hwm bl (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) := by
  obtain ⟨hp1, hlcn, hpg3, hnm1, hpg, hroot0, hkid, honly, hnself⟩ :=
    col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have hlook := col_look W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI
  have hpos := col_pos W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI
  have hother := col_other W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI
  have hnm' := col_nm B nl lc rc.nv.pgid' (colRoot rn rc sI)
  have hns' := col_ns B nl lc rc.nv.pgid' (colRoot rn rc sI)
  have hinj := nm_inj W hwm bl B hc
  have hnmc : B.nm !! rc.nv.pgid' = some lc := by rw [hpg3]; exact hlc
  have hnmo : ∀ c, c ≠ rc.nv.pgid' → (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).nm !! c = B.nm !! c := by
    intro c hcne; rw [hnm', if_neg hcne]
  have hcl := hc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hcl
  have hrn0 : B.bv.rootNode' ≠ null := by
    intro h0; have := (c3 h0).1; rw [this] at hrn; cases hrn
  have hnn := c8 nl rn hrn
  have hnc := c8 lc rc hrc
  have hroot : B.bv.rootNode' = nl := hnn.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
  have hchild : ∀ (q : Loc) (l' : Loc) (x : w64), B.nm !! x = some l' → x ≠ rc.nv.pgid' →
      (∀ r', B.ns !! l' = some r' → r'.nv.parent' = q) →
      ∃ r', (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns !! l' = some r' ∧
        r'.nv.parent' = (if q = lc then nl else q) := by
    intro q l' x hx hxn hpq
    obtain ⟨-, r0, hr0, -⟩ := c5 x l' hx
    have hl'c : l' ≠ lc := by intro he; rw [he] at hx; exact hxn (hinj _ _ _ hx hnmc)
    obtain ⟨r0', h1, -, h3⟩ := hlook l' r0 hr0 hl'c
    exact ⟨r0', h1, by rw [h3, hpq r0 hr0]⟩
  refine ⟨c1, c2, fun h0 => absurd h0 hrn0, fun _ => ?_, ?_, c6, fun h0 => absurd h0 hroot0, ?_, ?_, ?_⟩
  · have h4 := c4 hrn0
    show (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).nm !! B.ib.root' = some B.bv.rootNode'
    rw [hnmo _ (by intro he; rw [he, hnmc] at h4; rw [hroot] at h4; exact hlcn (Option.some.inj h4))]
    exact h4
  · intro c l hl
    rw [hnm'] at hl
    split at hl
    · cases hl
    rename_i hcn
    obtain ⟨hnn', r0, hr0, hp0⟩ := c5 c l hl
    have hlc' : l ≠ lc := by intro he; rw [he] at hl; exact hcn (hinj _ _ _ hl hnmc)
    obtain ⟨r0', h1, h2, -⟩ := hlook l r0 hr0 hlc'
    exact ⟨hnn', r0', h1, by rw [h2]; exact hp0⟩
  · intro y ry' hy
    rw [hns'] at hy
    split at hy
    · -- the root
      rename_i hyn
      cases hy; subst y
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hnn
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16⟩ := hnc
      refine ⟨n1, m2, m3, m4, m5, n6, by show _ !! rn.nv.pgid' = _; rw [hnmo _ hpg]; exact n7, n8, n9, n10, m11, fun hb => ?_,
        fun _ => hroot, fun hp => absurd hpn hp, m15, fun c hcin => ?_⟩
      · obtain ⟨a1, a2, a3⟩ := m12 hb
        refine ⟨a1, a2, fun x hx => ?_⟩
        obtain ⟨k1, k2, k3⟩ := a3 x hx
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        have hxn : x.pgid ≠ rc.nv.pgid' := fun he => hlcn (honly lc rc j x hrc hb hj he)
        refine ⟨k1, fun l' hl' => ?_, fun hn => by rw [hnmo _ hxn] at hn; exact k3 hn⟩
        rw [hnmo _ hxn] at hl'
        obtain ⟨r', h1, h2⟩ := hchild lc l' x.pgid hl' hxn (fun r' hr' => by
          obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
        exact ⟨r', h1, by rw [h2, if_pos rfl]⟩
      · obtain ⟨rc0, hrc0, hpc⟩ := m16 c hcin
        have hcc : c ≠ lc := by
          intro he; rw [he, hrc] at hrc0; cases hrc0
          rcases hnself lc rc hrc with h | h
          · exact h hpc
          · rw [hp1] at h; exact (c5 _ _ hnm1).1 h
        obtain ⟨rc', h1, -, h3⟩ := hlook c rc0 hrc0 hcc
        exact ⟨rc', h1, by rw [h3, hpc, if_pos rfl]⟩
    split at hy
    · cases hy
    rename_i hyn hyc
    obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := c8 y ry hry
    have hpgy : ry.nv.pgid' ≠ rc.nv.pgid' := by
      intro he; rw [he] at n7; exact hyc (Option.some.inj (n7.symm.trans hnmc))
    have hgen : ∀ ry' : NRec, ry'.ws = ry.ws → ry'.cs = ry.cs → ry'.ins = ry.ins → ry'.key = ry.key →
        ry'.ksrc = ry.ksrc → ry'.nv.bucket' = ry.nv.bucket' → ry'.nv.isLeaf' = ry.nv.isLeaf' →
        ry'.nv.spilled' = ry.nv.spilled' → ry'.nv.key' = ry.nv.key' → ry'.nv.pgid' = ry.nv.pgid' →
        ry'.nv.parent' = (if ry.nv.parent' = lc then nl else ry.nv.parent') →
        nodeClean W hwm bl (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) y ry' := by
      intro ry' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      refine ⟨by rw [e6]; exact n1, by rw [e3, e1]; exact n2, by rw [e1]; exact n3,
        by rw [e1]; exact n4, by rw [e1]; exact n5, by rw [e8]; exact n6,
        by rw [e10, hnmo _ hpgy]; exact n7, by rw [e10]; exact n8, by rw [e10]; exact n9,
        by rw [e9, e4, e5]; exact n10, by rw [e7, e1]; exact n11, ?_, ?_, ?_, by rw [e2]; exact n15, ?_⟩
      · intro hb
        rw [e7] at hb; rw [e1]
        obtain ⟨a1, a2, a3⟩ := n12 hb
        refine ⟨a1, a2, fun x hx => ?_⟩
        obtain ⟨k1, k2, k3⟩ := a3 x hx
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        have hxn : x.pgid ≠ rc.nv.pgid' := fun he => hyn (honly y ry j x hry hb hj he)
        refine ⟨k1, fun l' hl' => ?_, fun hn => by rw [hnmo _ hxn] at hn; exact k3 hn⟩
        rw [hnmo _ hxn] at hl'
        obtain ⟨r', h1, h2⟩ := hchild y l' x.pgid hl' hxn (fun r' hr' => by
          obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
        exact ⟨r', h1, by rw [h2, if_neg hyc]⟩
      · intro hp
        rw [e11] at hp
        split at hp
        · exact absurd hp (c5 _ _ hnm1).1
        · exact n13 hp
      · intro hp
        rw [e11]
        split
        · rename_i hpr
          obtain ⟨rq, hrq, hbq, -, x, hx, hxp⟩ := n14 (by rw [hpr]; exact (c5 _ _ hlc).1)
          rw [hpr, hrc] at hrq; cases hrq
          obtain ⟨rq', hrq', -, hiq, -⟩ := n14 (by rw [hpr]; exact (c5 _ _ hlc).1)
          rw [hpr, hrc] at hrq'; cases hrq'
          exact ⟨colRoot rn rc sI, by rw [hns', if_pos rfl], hbq, hiq, x, hx, by rw [e10]; exact hxp⟩
        · rename_i hpr
          have hp' : ry.nv.parent' ≠ null := by rw [e11, if_neg hpr] at hp; exact hp
          obtain ⟨rq, hrq, hbq, hiq, x, hx, hxp⟩ := n14 hp'
          have hqn : ry.nv.parent' ≠ nl := fun he => hyc (hkid y ry hry he)
          rw [hother _ rq hrq hqn hpr]
          refine ⟨_, rfl, ?_, ?_, x, ?_, by rw [e10]; exact hxp⟩ <;> split <;> assumption
      · intro c hcin
        rw [e2] at hcin
        obtain ⟨rc0, hrc0, hpc⟩ := n16 c hcin
        have hcc : c ≠ lc := by
          intro he; rw [he, hrc] at hrc0; cases hrc0; rw [hp1] at hpc; exact hyn hpc.symm
        obtain ⟨rc', h1, -, h3⟩ := hlook c rc0 hrc0 hcc
        exact ⟨rc', h1, by rw [h3, hpc, if_neg hyc]⟩
    split
    · exact hgen _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [if_pos ‹_›])
    · exact hgen _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [if_neg ‹_›])
  · intro l1 i1 q1 l2 i2 q2 h1 h2 hne d hd
    obtain ⟨n1, p1'⟩ := hpos l1 i1 q1 h1
    obtain ⟨n2, p2'⟩ := hpos l2 i2 q2 h2
    refine c9 _ _ q1 _ _ q2 p1' p2' ?_ d hd
    intro he; apply hne
    simp only [Prod.mk.injEq] at he ⊢
    refine ⟨?_, he.2⟩
    have := he.1
    by_cases a1 : l1 = nl <;> by_cases a2 : l2 = nl
    · rw [a1, a2]
    · rw [if_pos a1, if_neg a2] at this; exact absurd this.symm n2
    · rw [if_neg a1, if_pos a2] at this; exact absurd this n1
    · rw [if_neg a1, if_neg a2] at this; exact this
  · intro l j q hp d hd
    obtain ⟨-, p'⟩ := hpos l j q hp
    rw [hnm']; split
    · rfl
    · exact c10 _ _ q p' d hd

theorem col_keys (sI : GoSlice) (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : rblKeysB W B bnd (some nl)) :
    rblKeysB W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) (fun x => if x = nl then bnd lc else bnd x)
      none := by
  obtain ⟨hp1, hlcn, hpg3, hnm1, hpg, hroot0, hkid, honly, hnself⟩ :=
    col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have hother := col_other W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI
  have hnm' := col_nm B nl lc rc.nv.pgid' (colRoot rn rc sI)
  have hns' := col_ns B nl lc rc.nv.pgid' (colRoot rn rc sI)
  have hinj := nm_inj W hwm bl B hc
  have hnmc : B.nm !! rc.nv.pgid' = some lc := by rw [hpg3]; exact hlc
  have hnmo : ∀ c, c ≠ rc.nv.pgid' → (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).nm !! c = B.nm !! c := by
    intro c hcne; rw [hnm', if_neg hcne]
  have hrn0 : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc.2.2.1 h0).1; rw [this] at hrn; cases hrn
  have hroot : B.bv.rootNode' = nl := (hc.2.2.2.2.2.2.2.1 nl rn hrn).2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
  obtain ⟨k1, k2, k3⟩ := hk
  have hbn : ∀ x, x ≠ nl → (fun x => if x = nl then bnd lc else bnd x) x = bnd x := by
    intro x hx; simp [hx]
  have hbnl : (fun x => if x = nl then bnd lc else bnd x) nl = bnd lc := by simp
  have hkidrec : ∀ (l' : Loc) (x : w64), B.nm !! x = some l' → x ≠ rc.nv.pgid' → ∀ r0, B.ns !! l' = some r0 →
      r0.nv.parent' ≠ null →
      ∃ r', (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns !! l' = some r' ∧ r'.nv.isLeaf' = r0.nv.isLeaf' := by
    intro l' x hx hxn r0 hr0 hpar
    have hl'c : l' ≠ lc := by intro he; rw [he] at hx; exact hxn (hinj _ _ _ hx hnmc)
    have hln : l' ≠ nl := by intro he; rw [he, hrn] at hr0; cases hr0; exact hpar hpn
    rw [hother l' r0 hr0 hln hl'c]
    exact ⟨_, rfl, by split <;> rfl⟩
  have hparn : ∀ y ry l', B.ns !! y = some ry → ry.nv.isLeaf' = false → ∀ x ∈ ry.ws, B.nm !! x.pgid = some l' →
      ∀ r0, B.ns !! l' = some r0 → r0.nv.parent' ≠ null := by
    intro y ry l' hy hb x hx hl' r0 hr0
    obtain ⟨-, -, hkk⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.1 hb
    obtain ⟨r1, h1, hp⟩ := (hkk x hx).2.1 l' hl'
    rw [hr0] at h1; cases h1; rw [hp]; exact (hc.2.2.2.2.1 _ _ (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.1).1
  refine ⟨k1, fun r0 h0 => ?_, fun y ry' hy => ?_⟩
  · change (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns !! B.bv.rootNode' = some r0 at h0
    rw [hroot, hns', if_pos rfl] at h0; cases h0; exact hpn
  rw [hns'] at hy
  split at hy
  · -- the root
    rename_i hyn
    cases hy; subst y
    obtain ⟨l1, -, l3, -, l5⟩ := k3 lc rc hrc
    refine ⟨by rw [hbnl]; exact l1, fun hp => absurd hpn hp, fun hb => ?_,
      fun _ _ _ hp => absurd hpn hp, l5⟩
    obtain ⟨a1, a2, kind, a3⟩ := l3 hb
    refine ⟨fun _ => a1 (by intro he; cases he; exact hlcn rfl), by rw [hbnl]; exact a2, kind,
      fun j x hx => ?_⟩
    obtain ⟨b1, b2⟩ := a3 j x hx
    have hxn : x.pgid ≠ rc.nv.pgid' := fun he => hlcn (honly lc rc j x hrc hb hx he)
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rw [hnmo _ hxn] at hl'
      obtain ⟨r0, hr0, hk0⟩ := b1 l' hl'
      obtain ⟨r', h1, h2⟩ := hkidrec l' x.pgid hl' hxn r0 hr0
        (hparn lc rc l' hrc hb x (List.mem_of_getElem? hx) hl' r0 hr0)
      exact ⟨r', h1, by rw [h2]; exact hk0⟩
    · rw [hnmo _ hxn] at hn
      rw [hbnl]; exact b2 hn
  split at hy
  · cases hy
  rename_i hyn hyc
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  obtain ⟨n1, n2, n3, n4, n5⟩ := k3 y ry hry
  have hdy : some nl ≠ some y := by intro he; cases he; exact hyn rfl
  have hgen : ∀ ry' : NRec, ry'.ws = ry.ws → ry'.key = ry.key → ry'.nv.isLeaf' = ry.nv.isLeaf' →
      ry'.nv.key' = ry.nv.key' → ry'.nv.pgid' = ry.nv.pgid' → ry'.nv.unbalanced' = ry.nv.unbalanced' →
      ry'.nv.parent' = (if ry.nv.parent' = lc then nl else ry.nv.parent') →
      rblNodeKeys W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) (fun x => if x = nl then bnd lc else bnd x)
        none y ry' := by
    intro ry' e1 e2 e3 e4 e5 e6 e7
    refine ⟨by rw [e1, hbn _ hyn]; exact n1, fun hp => ?_, fun hb => ?_, fun _ hlf hu hp => ?_,
      by rw [e3, e1]; exact n5⟩
    · rw [e7] at hp
      have hp0 : ry.nv.parent' ≠ null := by
        split at hp
        · rename_i h; rw [h]; exact (hc.2.2.2.2.1 _ _ hlc).1
        · exact hp
      obtain ⟨hkey, rq, i, x, hrq, hx, hxp, hxk, hbnd⟩ := n2 hp0
      refine ⟨by rw [e4]; exact hkey, ?_⟩
      rw [e7, e5, e2, hbn _ hyn]
      by_cases hpr : ry.nv.parent' = lc
      · rw [if_pos hpr]
        rw [hpr, hrc] at hrq; cases hrq
        refine ⟨colRoot rn rc sI, i, x, by rw [hns', if_pos rfl], hx, hxp, hxk, ?_⟩
        rw [hbnl]; rw [hpr] at hbnd; exact hbnd
      · rw [if_neg hpr]
        have hqn : ry.nv.parent' ≠ nl := fun he => hyc (hkid y ry hry he)
        refine ⟨_, i, x, hother _ rq hrq hqn hpr, ?_, hxp, hxk, ?_⟩
        · split <;> exact hx
        · rw [hbn _ hqn]; split <;> exact hbnd
    · rw [e3] at hb
      obtain ⟨a1, a2, kind, a3⟩ := n3 hb
      refine ⟨fun _ => by rw [e1]; exact a1 hdy, by rw [e1, hbn _ hyn]; exact a2, kind,
        fun j x hx => ?_⟩
      rw [e1] at hx
      obtain ⟨b1, b2⟩ := a3 j x hx
      have hxn : x.pgid ≠ rc.nv.pgid' := fun he => hyn (honly y ry j x hry hb hx he)
      refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
      · rw [hnmo _ hxn] at hl'
        obtain ⟨r0, hr0, hk0⟩ := b1 l' hl'
        obtain ⟨r', h1, h2⟩ := hkidrec l' x.pgid hl' hxn r0 hr0
          (hparn y ry l' hry hb x (List.mem_of_getElem? hx) hl' r0 hr0)
        exact ⟨r', h1, by rw [h2]; exact hk0⟩
      · rw [hnmo _ hxn] at hn
        rw [hbn _ hyn, e1]; exact b2 hn
    · rw [e3] at hlf; rw [e6] at hu; rw [e1]
      have hp0 : ry.nv.parent' ≠ null := by
        rw [e7] at hp; split at hp
        · rename_i h; rw [h]; exact (hc.2.2.2.2.1 _ _ hlc).1
        · exact hp
      exact n4 hdy hlf hu hp0
  split
  · exact hgen _ rfl rfl rfl rfl rfl rfl (by rw [if_pos ‹_›])
  · exact hgen _ rfl rfl rfl rfl rfl rfl (by rw [if_neg ‹_›])

theorem col_acyc (sI : GoSlice) : rblAcyc (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) := by
  obtain ⟨hp1, hlcn, -⟩ := col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  obtain ⟨ht, hh⟩ := ha
  have h1 := hh lc rc hrc (by rw [hp1]; exact (hc.2.2.2.2.1 _ _ (hc.2.2.2.2.2.2.2.1 nl rn hrn).2.2.2.2.2.2.1).1)
  rw [hp1] at h1
  refine ⟨ht, fun y ry' hy hp => ?_⟩
  rw [col_ns] at hy
  split at hy
  · cases hy; exact absurd hpn hp
  split at hy
  · cases hy
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  by_cases hpr : ry.nv.parent' = lc
  · simp only [if_pos hpr] at hp ⊢
    have := hh y ry hry (by rw [hpr]; exact (hc.2.2.2.2.1 _ _ hlc).1)
    rw [hpr] at this; omega
  · simp only [if_neg hpr] at hp ⊢
    exact hh y ry hry hp

theorem col_ht (sI : GoSlice) (hht : rblHt W B) : rblHt W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) := by
  obtain ⟨hp1, hlcn, hpg3, hnm1, hpg, hroot0, hkid, honly, -⟩ :=
    col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  obtain ⟨ht, pht, hp, hh⟩ := hht
  have hnm' := col_nm B nl lc rc.nv.pgid' (colRoot rn rc sI)
  have hnmc : B.nm !! rc.nv.pgid' = some lc := by rw [hpg3]; exact hlc
  -- a child is not the root
  have hnotn : ∀ y ry x l', B.ns !! y = some ry → ry.nv.isLeaf' = false → x ∈ ry.ws →
      B.nm !! x.pgid = some l' → l' ≠ nl := by
    intro y ry x l' hy hb hx hl' he
    obtain ⟨-, -, hkk⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.1 hb
    obtain ⟨r1, h1, hpr⟩ := (hkk x hx).2.1 l' hl'
    rw [he, hrn] at h1; cases h1; rw [hpn] at hpr
    exact (hc.2.2.2.2.1 _ _ (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.1).1 hpr.symm
  have hent : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → ∀ x ∈ ry.ws, x.pgid ≠ rc.nv.pgid' →
      (∀ l', (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).nm !! x.pgid = some l' →
        (if l' = nl then ht lc else ht l') + 1 = ht y) ∧
      ((colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).nm !! x.pgid = none → pht (uint.nat x.pgid) + 1 = ht y) := by
    intro y ry hy hb x hx hxn
    rw [hnm', if_neg hxn]
    obtain ⟨a1, a2⟩ := (hh y ry hy).2 hb x hx
    exact ⟨fun l' hl' => by rw [if_neg (hnotn y ry x l' hy hb hx hl')]; exact a1 l' hl', a2⟩
  refine ⟨fun x => if x = nl then ht lc else ht x, pht, hp, fun y ry' hy => ?_⟩
  rw [col_ns] at hy
  split at hy
  · rename_i hyn; cases hy; subst y
    refine ⟨fun hl => by simp only [if_pos rfl]; exact (hh lc rc hrc).1 hl, fun hb x hx => ?_⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    have := hent lc rc hrc hb x hx (fun he => hlcn (honly lc rc j x hrc hb hj he))
    simp only [if_pos rfl]; exact this
  split at hy
  · cases hy
  rename_i hyn hyc
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  have key : ((if ry.nv.parent' = lc then ({ ry with nv := { ry.nv with parent' := nl } } : NRec) else ry).nv.isLeaf' = ry.nv.isLeaf') ∧
      ((if ry.nv.parent' = lc then ({ ry with nv := { ry.nv with parent' := nl } } : NRec) else ry).ws = ry.ws) := by
    split <;> exact ⟨rfl, rfl⟩
  rw [key.1, key.2]
  simp only [if_neg hyn]
  refine ⟨(hh y ry hry).1, fun hb x hx => ?_⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  exact hent y ry hry hb x hx (fun he => hyn (honly y ry j x hry hb hj he))

theorem col_entryIn (sI : GoSlice) (kk v : List w8) (h : entryIn W B kk v) :
    entryIn W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) kk v := by
  obtain ⟨hp1, hlcn, hpg3, hnm1, hpg, hroot0, hkid, honly, -⟩ :=
    col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have hns' := col_ns B nl lc rc.nv.pgid' (colRoot rn rc sI)
  have hnmc : B.nm !! rc.nv.pgid' = some lc := by rw [hpg3]; exact hlc
  rcases h with ⟨y, ry, x, hy, hl, hx, hk, hbk, hv⟩ | ⟨c, q, pgq, j, hpos, ho, hpq, hlq, hj, hkq, hfq, hvq⟩
  · have hyn : y ≠ nl := by intro he; rw [he, hrn] at hy; cases hy; rw [hbr] at hl; cases hl
    by_cases hyc : y = lc
    · subst hyc; rw [hrc] at hy; cases hy
      exact Or.inl ⟨nl, colRoot rn rc sI, x, by rw [hns', if_pos rfl], hl, hx, hk, hbk, hv⟩
    by_cases hpr : ry.nv.parent' = lc
    · exact Or.inl ⟨y, { ry with nv := { ry.nv with parent' := nl } }, x,
        by rw [hns', if_neg hyn, if_neg hyc, hy]; simp only [Option.map_some, hpr, ↓reduceIte], hl, hx, hk, hbk, hv⟩
    · exact Or.inl ⟨y, ry, x,
        by rw [hns', if_neg hyn, if_neg hyc, hy]; simp only [Option.map_some, hpr, ↓reduceIte], hl, hx, hk, hbk, hv⟩
  · refine Or.inr ⟨c, q, pgq, j, ?_, ho, hpq, hlq, hj, hkq, hfq, hvq⟩
    unfold posRoot at hpos ⊢
    rcases hpos with h1 | ⟨y, j0, ⟨ry, x, hy, hyb, hx, hxc, hn⟩, hlt⟩
    · exact Or.inl h1
    right
    have hxn : x.pgid ≠ rc.nv.pgid' := by intro he; rw [hxc] at he; rw [he, hnmc] at hn; cases hn
    have hn' : (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).nm !! W64 (c : Int) = none := by
      rw [col_nm, if_neg (by rw [← hxc]; exact hxn)]; exact hn
    have hyn : y ≠ nl := by
      intro he; rw [he, hrn] at hy; cases hy; rw [hws] at hx
      have : j0 = 0 ∧ x = w0 := by
        cases j0 with
        | zero => simp at hx; exact ⟨rfl, hx.symm⟩
        | succ n => simp at hx
      rw [← hxc, this.2, hlc] at hn; cases hn
    by_cases hyc : y = lc
    · subst y; rw [hrc] at hy; cases hy
      exact ⟨nl, j0, ⟨colRoot rn rc sI, x, by rw [hns', if_pos rfl], hyb, hx, hxc, hn'⟩, hlt⟩
    by_cases hpr : ry.nv.parent' = lc
    · exact ⟨y, j0, ⟨{ ry with nv := { ry.nv with parent' := nl } }, x,
        by rw [hns', if_neg hyn, if_neg hyc, hy]; simp only [Option.map_some, hpr, ↓reduceIte],
        hyb, hx, hxc, hn'⟩, hlt⟩
    · exact ⟨y, j0, ⟨ry, x,
        by rw [hns', if_neg hyn, if_neg hyc, hy]; simp only [Option.map_some, hpr, ↓reduceIte],
        hyb, hx, hxc, hn'⟩, hlt⟩

theorem col_unbal (sI : GoSlice) (y : Loc) (ry' : NRec)
    (hy : (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y = some ry') (hu : ry'.nv.unbalanced' = true) :
    y = nl ∧ rn.nv.unbalanced' = true ∨
      (y ≠ lc ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid') := by
  rw [col_ns] at hy
  split at hy
  · rename_i h; cases hy; exact Or.inl ⟨h, hu⟩
  split at hy
  · cases hy
  rename_i _ hyc
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  refine Or.inr ⟨hyc, ry, hry, ?_, ?_⟩ <;> split at hu <;> first | exact hu | (split <;> rfl)

end col

/-- A branch root with one child collapsed into it: the bucket in the invariant, no deficient
node. -/
theorem rbl_col (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (nl : Loc) (rn : NRec) (w0 : WEntry)
    (lc : Loc) (rc : NRec) (sI : GoSlice) (HB : rblB W hwm bl B (some nl)) (hrn : B.ns !! nl = some rn)
    (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null) (hws : rn.ws = [w0])
    (hlc : B.nm !! w0.pgid = some lc) (hrc : B.ns !! lc = some rc) :
    rblB W hwm bl (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) none ∧
      (∀ kk v, entryIn W B kk v → entryIn W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) kk v) ∧
      (∀ y ry', (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y = some ry' →
        ry'.nv.unbalanced' = true → y = nl ∧ rn.nv.unbalanced' = true ∨
        (y ≠ lc ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid')) := by
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hht⟩ := HB
  exact ⟨⟨col_clean W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI,
      ⟨_, col_keys W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI bnd hk⟩,
      col_acyc W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI,
      col_ht W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI hht⟩,
    fun kk v h => col_entryIn W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI kk v h,
    fun y ry' hy hu => col_unbal W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI y ry' hy hu⟩

end pure

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

open Classical Iris.ProofMode in
/-- The tokens of the collapsed root: its page's and the child's positions', and the child's
page's. -/
theorem nodeToks_col (γ : GName) (W : WView) (B B' : BRec) (rn rc rn' : NRec) (hbm : B'.bm = B.bm)
    (hp : rn'.nv.pgid' = rn.nv.pgid') (hws : rn'.ws = rc.ws) (hl : rn'.nv.isLeaf' = rc.nv.isLeaf')
    (hnm : rc.nv.isLeaf' = false → ∀ x ∈ rc.ws, B'.nm !! x.pgid = B.nm !! x.pgid) :
    nodeToks (GF := GF) γ W B rn ∗ nodeToks γ W B rc ⊢ nodeToks γ W B' rn' ∗
      (if rc.nv.pgid' = W64 0 then emp else
        pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat rc.nv.pgid')) W.pages)) := by
  iintro ⟨Hn, Hc⟩
  unfold nodeToks
  icases Hn with ⟨Ho, -⟩
  icases Hc with ⟨Hoc, Hl⟩
  rw [hp, hws, hl, opened_eq B B' hbm]
  iframe Ho Hoc
  iapply (BigSepL.bigSepL_mono ?_) $$ Hl
  intro j x hx
  by_cases hlf : rc.nv.isLeaf' = true
  · simp only [hlf, ↓reduceIte]; exact .rfl
  · have hf : rc.nv.isLeaf' = false := by simpa using hlf
    simp only [hlf, Bool.false_eq_true, ↓reduceIte]
    rw [hnm hf x (List.mem_of_getElem? hx)]

open Classical Iris.ProofMode in
/-- The tokens after the collapse, and the child's page's. -/
theorem col_toks (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (nl : Loc) (rn : NRec)
    (w0 : WEntry) (lc : Loc) (rc : NRec)
    (hc : bktClean W hwm bl B) (ha : rblAcyc B) (hrn : B.ns !! nl = some rn)
    (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null) (hws : rn.ws = [w0])
    (hlc : B.nm !! w0.pgid = some lc) (hrc : B.ns !! lc = some rc) (sI : GoSlice) :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) ∗
      (if rc.nv.pgid' = W64 0 then emp else
        pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat rc.nv.pgid')) W.pages)) := by
  obtain ⟨hp1, hlcn, hpg3, hnm1, hpg, hroot0, hkid, honly, -⟩ :=
    col_basic W hwm bl B nl rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have hnm' := col_nm B nl lc rc.nv.pgid' (colRoot rn rc sI)
  have hrn0 : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc.2.2.1 h0).1; rw [this] at hrn; cases hrn
  let f : NRec → NRec := fun x => if x.nv.parent' = lc then { x with nv := { x.nv with parent' := nl } } else x
  let D0 : GMap Loc NRec := GMap.delete nl (GMap.delete lc B.ns)
  have hD0 : ∀ y, D0 !! y = if y = nl ∨ y = lc then none else B.ns !! y := by
    intro y
    show (GMap.delete nl (GMap.delete lc B.ns)) !! y = _
    by_cases h1 : y = nl
    · subst h1; rw [GMap.lookup_delete, if_pos (Or.inl rfl)]
    rw [GMap.lookup_delete_ne _ (Ne.symm h1)]
    by_cases h2 : y = lc
    · subst h2; rw [GMap.lookup_delete, if_pos (Or.inr rfl)]
    rw [GMap.lookup_delete_ne _ (Ne.symm h2), if_neg (by rintro (h | h) <;> contradiction)]
  have he : (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).ns =
      <[nl := colRoot rn rc sI]> (GMap.fmap f D0) := by
    apply GMap.ext; intro y
    rw [col_ns, rf_lookup, GMap.lookup_fmap, hD0]
    by_cases h1 : y = nl
    · rw [if_pos h1, if_pos h1]
    rw [if_neg h1, if_neg h1]
    by_cases h2 : y = lc
    · rw [if_pos h2, if_pos (Or.inr h2)]; rfl
    rw [if_neg h2, if_neg (by rintro (h | h) <;> contradiction)]
  have hfm : (GMap.fmap f D0 : GMap Loc NRec) = Iris.Std.PartialMap.map f D0 := by
    apply GMap.ext; intro y
    show (GMap.fmap f D0) !! y = Std.get? (Iris.Std.PartialMap.map f D0) y
    rw [GMap.lookup_fmap, Iris.Std.LawfulPartialMap.get?_map]; rfl
  have hnmC : rc.nv.isLeaf' = false → ∀ x ∈ rc.ws,
      (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)).nm !! x.pgid = B.nm !! x.pgid := by
    intro hb x hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    have hxn : x.pgid ≠ rc.nv.pgid' := fun he => hlcn (honly lc rc j x hrc hb hj he)
    rw [hnm', if_neg hxn]
  unfold bktToks
  rw [if_neg hrn0]
  show _ ⊢ (if B.bv.rootNode' = null then _ else _) ∗ _
  rw [if_neg hrn0, he]
  have g1 : Std.get? B.ns lc = some rc := hrc
  have g2 : Std.get? (Std.delete B.ns lc) nl = some rn := by
    show (GMap.delete lc B.ns) !! nl = _; rw [GMap.lookup_delete_ne _ hlcn]; exact hrn
  iintro H
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r) g1).1 $$ H
    with ⟨Hc, H⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r) g2).1 $$ H
    with ⟨Hn, H⟩
  icases nodeToks_col γ W B (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) rn rc (colRoot rn rc sI) rfl rfl rfl
    rfl hnmC $$ [Hn Hc] with ⟨Hn, Hown⟩
  · iframe
  · iframe Hown
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ x => nodeToks (GF := GF) γ W
      (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) x)
      (show Std.get? (GMap.fmap f D0) nl = none by
        show (GMap.fmap f D0) !! nl = none
        rw [GMap.lookup_fmap, hD0, if_pos (Or.inl rfl)]; rfl)).2
    iframe Hn
    rw [hfm, BigSepM.bigSepM_map]
    have hD0' : (Std.delete (Std.delete B.ns lc) nl : GMap Loc NRec) = D0 := rfl
    rw [hD0']
    iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
      (Ψ := fun _ x => nodeToks (GF := GF) γ W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) (f x)) ?_) $$ H
    intro y ry hy
    change D0 !! y = some ry at hy
    rw [hD0] at hy
    split at hy
    · cases hy
    rename_i hyn
    have hyp : y ≠ nl := fun h => hyn (Or.inl h)
    refine BIBase.Entails.trans (nodeToks_congr γ W B (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) ry ry
      rfl rfl rfl rfl ?_) ?_
    · intro hlf x hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      have hxn : x.pgid ≠ rc.nv.pgid' := fun he => hyp (honly y ry j x hy hlf hj he)
      rw [hnm', if_neg hxn]
    · show nodeToks γ W _ ry ⊢ nodeToks γ W _ (if ry.nv.parent' = lc then _ else ry)
      split
      · exact (BiEntails.of_eq (nodeToks_eq γ W (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI))
          (colBkt B nl lc rc.nv.pgid' (colRoot rn rc sI)) ry _ rfl rfl rfl rfl rfl)).2
      · exact .rfl

end toks

end bbolt
end EtcdGrove
end Perennial
