/-
The writer's logical trees as finite trees (U8b, `notes/bbolt-proof-plan.md`): `rtOK X bl`, a
finite tree of bucket `bl`'s logical tree from its root position, of height below the walks'
fuel, its leaves at one depth. At `Commit` every bucket has one (`rtOK_init`: from `wOK` and the
view's page heights, `viewWF`: before `Commit` the logical tree has its pages' shape, `txPg`).
It gives the walks (`leaves_rt`, `positions_rt`, `leafDepthOK_rt`). The records locate the
changed positions (`edge_mat`, `root_mat`: a materialized node occurs only under its parent's
position, the root node at the root), and a change of a bucket's records off some positions
keeps `ltree` there (`ltree_frame`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTreeSteps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rtx
variable [GooseExts]
set_option linter.unusedSectionVars false

/-! ## Helpers: what `ltree` reads -/

theorem w64_toNat_cast (x : w64) : W64 (x.toNat : Int) = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem branchPgid_cast (pg : List w8) (i : Nat) :
    (W64 (branchPgid pg i : Int)).toNat = branchPgid pg i := by
  unfold branchPgid; rw [w64_toNat_cast]

theorem pageW_pgid_branch (pg : List w8) (i : Nat) (h : pageFlags pg = branchPageFlag) :
    (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
  have hne : pageFlags pg ≠ leafPageFlag := by rw [h]; decide
  simp [pageW, hne]

theorem mem_pageWs (pg : List w8) (w : WEntry) (h : w ∈ pageWs pg) :
    ∃ i, i < pageCount pg ∧ w = pageW pg i := by
  simp only [pageWs, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, rfl⟩

theorem ltree_mat (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) (q : w64) (l : Loc) (r : NRec) (hq : B.nm !! q = some l)
    (hr : B.ns !! l = some r) : ltree X bl q = some (r.nv.isLeaf', r.ws) := by
  simp only [ltree, hb, resolve, h0, ↓reduceIte, hq, hr, Option.map_some]

theorem ltree_unmat (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) (q : w64) (hq : B.nm !! q = none) (pg : List w8)
    (hpg : X.v.pages !! q.toNat = some pg) :
    ltree X bl q = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  simp only [ltree, hb, resolve, h0, ↓reduceIte, hq, wpageAt, hpg, Option.map_some]

theorem ltree_mat_inv (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) (q : w64) (l : Loc) (hq : B.nm !! q = some l) (lf : Bool)
    (ws : List WEntry) (h : ltree X bl q = some (lf, ws)) :
    ∃ r, B.ns !! l = some r ∧ r.nv.isLeaf' = lf ∧ r.ws = ws := by
  simp only [ltree, hb, resolve, h0, ↓reduceIte, hq] at h
  cases hr : B.ns !! l with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨r, rfl, h.1, h.2⟩

theorem ltree_unmat_inv (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) (q : w64) (hq : B.nm !! q = none) (lf : Bool)
    (ws : List WEntry) (h : ltree X bl q = some (lf, ws)) :
    ∃ pg, X.v.pages !! q.toNat = some pg ∧ decide (pageFlags pg = leafPageFlag) = lf ∧
      pageWs pg = ws := by
  simp only [ltree, hb, resolve, h0, ↓reduceIte, hq, wpageAt] at h
  cases hp : X.v.pages !! q.toNat with
  | none => rw [hp] at h; simp at h
  | some pg =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨pg, rfl, h.1, h.2⟩

/-- An inline bucket's logical tree is one leaf. -/
theorem ltree_inline_leaf (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' = W64 0) (q : w64)
    (lf : Bool) (ws : List WEntry) (h : ltree X bl q = some (lf, ws)) : lf = true := by
  obtain ⟨c1, -, -, -, -, -, c7, -⟩ := hc
  simp only [ltree, hb, resolve, h0, ↓reduceIte] at h
  by_cases hn : B.bv.rootNode' = null
  · simp only [hn, ↓reduceIte, wpageAt, h0] at h
    by_cases hq : q = W64 0
    · simp only [hq, ↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, (c1 h0 hn).2.2.2.1]; rfl
    · simp only [hq, ↓reduceIte] at h
      simp at h
  · simp only [hn, ↓reduceIte] at h
    cases hr : B.ns !! B.bv.rootNode' with
    | none => rw [hr] at h; simp at h
    | some r =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact c7 h0 _ r hr

/-! ## Helpers: materialized positions (`edge_mat`) -/

/-- Position `q` is materialized, or its page's subtree is well-formed and holds no
materialized page. -/
def posI (X : WX) (B : BRec) (q : w64) : Prop :=
  B.nm !! q ≠ none ∨ (treeWF X.v.pages X.t.mv.pgid'.toNat q.toNat ∧
    ∀ d, treeHas X.v.pages q.toNat d → B.nm !! W64 (d : Int) = none)

theorem posI_step (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' ≠ W64 0) (x : w64)
    (hx : posI X B x) (ws : List WEntry) (hl : ltree X bl x = some (false, ws)) (w : WEntry)
    (hw : w ∈ ws) : posI X B w.pgid ∧
      ∀ l r, B.nm !! w.pgid = some l → B.ns !! l = some r → B.nm !! x = some r.nv.parent' := by
  obtain ⟨-, -, -, -, -, -, -, c8, -, c10⟩ := hc
  cases hxm : B.nm !! x with
  | some lx =>
    obtain ⟨rx, hrx, hlf, hws⟩ := ltree_mat_inv X bl B hb h0 x lx hxm false ws hl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, n13, -⟩ := c8 lx rx hrx
    obtain ⟨-, -, hall⟩ := n13 hlf
    subst hws
    obtain ⟨-, hpar, hfree⟩ := hall w hw
    constructor
    · cases hcm : B.nm !! w.pgid with
      | some _ => left; rw [hcm]; simp
      | none =>
        right
        refine ⟨hfree hcm, ?_⟩
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
        exact c10 lx i w.pgid ⟨rx, w, hrx, hlf, hi, rfl, hcm⟩
    · intro l r hl hr
      obtain ⟨r', hr', hp⟩ := hpar l hl
      rw [hr] at hr'; cases hr'
      rw [hp]
  | none =>
    rcases hx with hx | ⟨hwf, hfree⟩
    · exact absurd hxm hx
    obtain ⟨pg, hpg, hlf, hws⟩ := ltree_unmat_inv X bl B hb h0 x hxm false ws hl
    cases hwf with
    | page _ pg' _ _ hpg' _ _ hptw =>
      rw [hpg] at hpg'; cases hpg'
      cases hptw with
      | leaf _ _ hfl _ _ => simp [hfl] at hlf
      | branch _ _ hfb _ hch =>
        subst hws
        obtain ⟨i, hi, rfl⟩ := mem_pageWs pg w hw
        have hpid := pageW_pgid_branch pg i hfb
        have hcwf := hch i hi
        have hsub : ∀ d, treeHas X.v.pages (branchPgid pg i) d → treeHas X.v.pages x.toNat d :=
          fun d h => treeHas.sub _ pg d hpg (pageHas.child pg i d hfb hi h)
        constructor
        · right
          rw [hpid, branchPgid_cast]
          exact ⟨hcwf, fun d h => hfree d (hsub d h)⟩
        · intro l r hl _
          exfalso
          obtain ⟨cpg, hcpg⟩ : ∃ cpg, X.v.pages !! branchPgid pg i = some cpg := by
            cases hcwf with
            | page _ cpg _ _ h _ _ _ => exact ⟨cpg, h⟩
          have := hfree _ (hsub _ (treeHas.root _ cpg hcpg))
          rw [← hpid] at this
          rw [this] at hl; cases hl

mutual
theorem posI_subs (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' ≠ W64 0) :
    ∀ s : RTree, ltIs (ltree X) bl s → posI X B s.pid → ∀ s' ∈ s.subs, posI X B s'.pid
  | .mk p lf ws cs, h, hI, s', hs' => by
    simp only [RTree.subs, List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · exact hI
    cases lf with
    | true => simp only [ltIs] at h; rw [h.2] at hs'; simp [RTree.subsL] at hs'
    | false =>
      simp only [ltIs] at h
      exact posI_subsL X bl B hb hc h0 ws cs h.2
        (fun w hw => (posI_step X bl B hb hc h0 p hI ws h.1 w hw).1) s' hs'
theorem posI_subsL (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' ≠ W64 0) :
    ∀ (ws : List WEntry) (cs : List RTree), ltIsL (ltree X) bl ws cs →
      (∀ w ∈ ws, posI X B w.pgid) → ∀ s' ∈ RTree.subsL cs, posI X B s'.pid
  | [], [], _, _, s', hs' => by simp [RTree.subsL] at hs'
  | w :: ws, t :: ts, h, hw, s', hs' => by
    simp only [ltIsL] at h
    simp only [RTree.subsL, List.mem_append] at hs'
    rcases hs' with hs' | hs'
    · exact posI_subs X bl B hb hc h0 t h.2.1 (by rw [h.1]; exact hw w (List.mem_cons_self ..))
        s' hs'
    · exact posI_subsL X bl B hb hc h0 ws ts h.2.2
        (fun w' h' => hw w' (List.mem_cons_of_mem _ h')) s' hs'
  | [], _ :: _, h, _, _, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _, _, _ => by simp only [ltIsL] at h
end

/-! ## Helpers: the initial tree (`rtOK_init`) -/

/-- Position `q` is materialized, or an unmaterialized well-formed page. -/
def posJ (X : WX) (B : BRec) (q : w64) : Prop :=
  (∃ l r, B.nm !! q = some l ∧ B.ns !! l = some r) ∨
    (B.nm !! q = none ∧ treeWF X.v.pages X.t.mv.pgid'.toNat q.toNat)

theorem posJ_of (X : WX) (bl : Loc) (B : BRec) (hc : bktClean X.v X.t.mv.pgid'.toNat bl B)
    (q : w64) (hwf : B.nm !! q = none → treeWF X.v.pages X.t.mv.pgid'.toNat q.toNat) :
    posJ X B q := by
  cases hq : B.nm !! q with
  | none => exact Or.inr ⟨hq, hwf hq⟩
  | some l =>
    obtain ⟨r, hr, -⟩ := (hc.2.2.2.2.1 q l hq).2
    exact Or.inl ⟨l, r, hq, hr⟩

theorem ltIsL_build (L : LTree) (bl : Loc) (Q : RTree → Prop) : ∀ ws : List WEntry,
    (∀ w ∈ ws, ∃ c, c.pid = w.pgid ∧ ltIs L bl c ∧ Q c) →
    ∃ cs, ltIsL L bl ws cs ∧ ∀ c ∈ cs, Q c
  | [], _ => ⟨[], by simp only [ltIsL], by simp⟩
  | w :: ws, h => by
    obtain ⟨c, h1, h2, h3⟩ := h w (List.mem_cons_self ..)
    obtain ⟨cs, h4, h5⟩ := ltIsL_build L bl Q ws (fun w' h' => h w' (List.mem_cons_of_mem _ h'))
    refine ⟨c :: cs, ⟨h1, h2, h4⟩, ?_⟩
    intro c' hc'
    simp only [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact h3
    · exact h5 c' hc'

theorem htL_le (H : Nat) : ∀ cs : List RTree, (∀ c ∈ cs, c.ht + 1 ≤ H) → RTree.htL cs ≤ H
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
    simp only [RTree.htL]
    have := h c (List.mem_cons_self ..)
    have := htL_le H cs (fun c' h' => h c' (List.mem_cons_of_mem _ h'))
    omega

theorem mem_dpsL (d x : Nat) : ∀ cs : List RTree, x ∈ RTree.dpsL d cs → ∃ c ∈ cs, x ∈ c.dps d
  | [], h => by simp [RTree.dpsL] at h
  | c :: cs, h => by
    simp only [RTree.dpsL, List.mem_append] at h
    rcases h with h | h
    · exact ⟨c, List.mem_cons_self .., h⟩
    · obtain ⟨c', h1, h2⟩ := mem_dpsL d x cs h
      exact ⟨c', List.mem_cons_of_mem _ h1, h2⟩

/-- The branch at `q` with the entries `ws` (each a child of height `H - 1`) is a tree of
height at most `H`, its leaves at depth `d + H`. -/
theorem branch_tree (L : LTree) (bl : Loc) (q : w64) (ws : List WEntry) (H : Nat)
    (hL : L bl q = some (false, ws))
    (hch : ∀ w ∈ ws, ∃ c, c.pid = w.pgid ∧ ltIs L bl c ∧
      (c.ht + 1 ≤ H ∧ ∀ d x, x ∈ c.dps (d + 1) → x = d + H)) :
    ∃ t, ltIs L bl t ∧ t.pid = q ∧ t.ht ≤ H ∧ ∀ d x, x ∈ t.dps d → x = d + H := by
  obtain ⟨cs, hcs, hQ⟩ := ltIsL_build L bl _ ws hch
  refine ⟨.mk q false ws cs, ⟨hL, hcs⟩, rfl, htL_le H cs (fun c hc => (hQ c hc).1), ?_⟩
  intro d x hx
  simp only [RTree.dps] at hx
  obtain ⟨c, hc, hx⟩ := mem_dpsL _ x cs hx
  exact (hQ c hc).2 d x hx

theorem build_tree (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' ≠ W64 0)
    (hpg : ∀ l r, B.ns !! l = some r → nodePg X.v B.ib.root' r) (pht : Nat → Nat)
    (hht : pageHts X.v.pages pht) : ∀ n q, posJ X B q → pht q.toNat < n →
    ∃ t, ltIs (ltree X) bl t ∧ t.pid = q ∧ t.ht ≤ pht q.toNat ∧
      ∀ d x, x ∈ t.dps d → x = d + pht q.toNat
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, q, hJ, hn => by
    -- a child `W64 (branchPgid pg i)` of the page `pg` at `q`
    have hkid : ∀ pg, X.v.pages !! q.toNat = some pg → pageFlags pg = branchPageFlag →
        ∀ i, i < pageCount pg → ∀ w : WEntry, w.pgid = W64 (branchPgid pg i : Int) →
        posJ X B w.pgid → ∃ c, c.pid = w.pgid ∧ ltIs (ltree X) bl c ∧
          (c.ht + 1 ≤ pht q.toNat ∧ ∀ d x, x ∈ c.dps (d + 1) → x = d + pht q.toNat) := by
      intro pg hpgq hfb i hi w hw hJw
      have he := (hht _ pg hpgq).2 hfb i hi
      have hnat : w.pgid.toNat = branchPgid pg i := by rw [hw, branchPgid_cast]
      obtain ⟨c, h1, h2, h3, h4⟩ := build_tree X bl B hb hc h0 hpg pht hht n w.pgid hJw
        (by rw [hnat]; omega)
      rw [hnat] at h3 h4
      exact ⟨c, h2, h1, by omega, fun d x hx => by have := h4 (d + 1) x hx; omega⟩
    rcases hJ with ⟨l, r, hq, hr⟩ | ⟨hq, hwf⟩
    · have hpid : r.nv.pgid' = q := by
        obtain ⟨r', hr', hp⟩ := (hc.2.2.2.2.1 q l hq).2
        rw [hr] at hr'; cases hr'; exact hp
      have hlt := ltree_mat X bl B hb h0 q l r hq hr
      obtain ⟨hpl, hpb⟩ := hpg l r hr
      cases hleaf : r.nv.isLeaf' with
      | true =>
        obtain ⟨pg, hpgq, hfl⟩ := (hpl hleaf).2 h0
        rw [hpid] at hpgq
        have h0h := (hht _ pg hpgq).1 hfl
        refine ⟨.mk q true r.ws [], ⟨by rw [hlt, hleaf], rfl⟩, rfl, ?_, ?_⟩
        · simp [RTree.ht, RTree.htL]
        · intro d x hx; simp only [RTree.dps, List.mem_singleton] at hx; omega
      | false =>
        obtain ⟨-, pg, hpgq, hfb, hlen, hws⟩ := hpb hleaf
        rw [hpid] at hpgq
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, n13, -⟩ := hc.2.2.2.2.2.2.2.1 l r hr
        obtain ⟨-, -, hall⟩ := n13 hleaf
        refine branch_tree _ bl q r.ws _ (by rw [hlt, hleaf]) (fun w hw => ?_)
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
        have hil : i < r.ws.length := by
          rcases (List.getElem?_eq_some_iff.mp hi) with ⟨h, -⟩; exact h
        exact hkid pg hpgq hfb i (by omega) w (hws i w hi)
          (posJ_of X bl B hc w.pgid (hall w hw).2.2)
    · cases hwf with
      | page _ pg _ _ hpgq _ _ hptw =>
        have hlt := ltree_unmat X bl B hb h0 q hq pg hpgq
        cases hptw with
        | leaf _ _ hfl _ _ =>
          have h0h := (hht _ pg hpgq).1 hfl
          refine ⟨.mk q true (pageWs pg) [], ⟨by rw [hlt]; simp [hfl], rfl⟩, rfl, ?_, ?_⟩
          · simp [RTree.ht, RTree.htL]
          · intro d x hx; simp only [RTree.dps, List.mem_singleton] at hx; omega
        | branch _ _ hfb _ hch =>
          have hne : pageFlags pg ≠ leafPageFlag := by rw [hfb]; decide
          refine branch_tree _ bl q (pageWs pg) _ (by rw [hlt]; simp [hne]) (fun w hw => ?_)
          obtain ⟨i, hi, rfl⟩ := mem_pageWs pg w hw
          have hpid := pageW_pgid_branch pg i hfb
          exact hkid pg hpgq hfb i hi _ hpid
            (posJ_of X bl B hc _ (fun _ => by rw [hpid, branchPgid_cast]; exact hch i hi))

/-- A page of height `h` heads a chain of `h + 1` distinct pages. -/
theorem pht_chain (pages : Pages) (hwm : Nat) (pht : Nat → Nat) (hht : pageHts pages pht) :
    ∀ h q, treeWF pages hwm q → pht q = h →
    ∃ l : List Nat, l.length = h + 1 ∧ l.Nodup ∧ ∀ x ∈ l, pht x ≤ h ∧ (pages !! x).isSome := by
  intro h
  induction h with
  | zero =>
    intro q hwf hq
    cases hwf with
    | page _ pg _ _ hpg _ _ _ =>
      refine ⟨[q], rfl, by simp, ?_⟩
      intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [hpg, hq]
  | succ h ih =>
    intro q hwf hq
    cases hwf with
    | page _ pg _ _ hpg _ _ hptw =>
      cases hptw with
      | leaf _ _ hfl _ _ =>
        have := (hht q pg hpg).1 hfl; omega
      | branch _ _ hfb hbwf hch =>
        have hpos : 0 < pageCount pg := hbwf.1
        have he := (hht q pg hpg).2 hfb 0 hpos
        obtain ⟨l, h1, h2, h3⟩ := ih _ (hch 0 hpos) (by omega)
        refine ⟨q :: l, by simp [h1], ?_, ?_⟩
        · refine List.nodup_cons.mpr ⟨fun hm => ?_, h2⟩
          have := (h3 q hm).1; omega
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp [hpg]; omega
          · have := h3 x hx; exact ⟨by omega, this.2⟩

/-- **Bucket `bl`'s logical tree is finite** (see the module doc). -/
def rtOK (X : WX) (bl : Loc) : Prop :=
  ∃ t, ltIs (ltree X) bl t ∧ t.pid = X.rootPid bl ∧ t.ht < X.fuel ∧ ∃ D, ∀ x ∈ t.dps 0, x = D

/-- **At `Commit`, every bucket's logical tree is finite**, its leaves at one depth (the root
page's height: before `Commit` a branch node's entries are its page's, `txPg`). -/
theorem rtOK_init (X : WX) (bl : Loc) (hok : wOK X) (hv : viewWF X.v)
    (hb : (X.t.bs !! bl).isSome) : rtOK X bl := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp hb
  have hc := (hok.1.2.2.2.2.2 bl B hB).1
  have hrp : X.rootPid bl = B.ib.root' := by
    simp only [WX.rootPid, hB, Option.map_some, Option.getD_some]
  by_cases h0 : B.ib.root' = W64 0
  · obtain ⟨ws, hws⟩ : ∃ ws, ltree X bl B.ib.root' = some (true, ws) := by
      by_cases hn : B.bv.rootNode' = null
      · refine ⟨pageWs B.ipg, ?_⟩
        have hg := (hc.1 h0 hn).2.2
        simp only [ltree, hB, resolve, h0, hn, ↓reduceIte, wpageAt, Option.map_some, hg.2.1,
          decide_true]
      · obtain ⟨r, hr, -⟩ := (hc.2.2.2.2.1 _ _ (hc.2.2.2.1 hn)).2
        refine ⟨r.ws, ?_⟩
        simp only [ltree, hB, resolve, h0, hn, ↓reduceIte, hr, Option.map_some,
          hc.2.2.2.2.2.2.1 h0 _ r hr]
    refine ⟨.mk B.ib.root' true ws [], ⟨hws, rfl⟩, hrp.symm, ?_, 0, ?_⟩
    · simp [RTree.ht, RTree.htL, WX.fuel]
    · intro x hx; simpa [RTree.dps] using hx
  · obtain ⟨C, hC, hvC⟩ := hv
    have hpages : C.pages = X.v.pages := congrArg View.pages hvC
    obtain ⟨pht, hpht⟩ := hC.1.2.2.2
    rw [hpages] at hpht
    have hJ : posJ X B B.ib.root' := by
      by_cases hn : B.bv.rootNode' = null
      · exact Or.inr ⟨by rw [(hc.2.2.1 hn).2]; rfl, (hc.2.1 h0).2 hn⟩
      · obtain ⟨r, hr, -⟩ := (hc.2.2.2.2.1 _ _ (hc.2.2.2.1 hn)).2
        exact Or.inl ⟨_, r, hc.2.2.2.1 hn, hr⟩
    have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat B.ib.root'.toNat := by
      rcases hJ with ⟨l, r, hq, hr⟩ | ⟨_, h⟩
      · obtain ⟨r', hr', hp⟩ := (hc.2.2.2.2.1 _ l hq).2
        rw [hr] at hr'; cases hr'
        obtain ⟨-, -, -, -, -, -, -, -, -, n10, -⟩ := hc.2.2.2.2.2.2.2.1 l r hr
        have := n10 h0
        rw [hp] at this; exact this
      · exact h
    obtain ⟨t, h1, h2, h3, h4⟩ := build_tree X bl B hB hc h0
      (fun l r hr => hok.2.2.1 bl B hB l r hr) pht hpht _ _ hJ (Nat.lt_succ_self _)
    obtain ⟨l, hl1, hl2, hl3⟩ := pht_chain _ _ pht hpht _ _ hwf rfl
    have hsz : l.length ≤ X.v.pages.size := by
      rw [GMap.size_eq_dom_list_length]
      exact List.Nodup.length_le_of_subset hl2
        (fun x hx => (GMap.mem_dom_list _ _).mpr (hl3 x hx).2)
    refine ⟨t, h1, by rw [h2, hrp], ?_, pht B.ib.root'.toNat, fun x hx => by
      have := h4 0 x hx; omega⟩
    unfold WX.fuel; omega

theorem leaves_rt (X : WX) (bl : Loc) (t : RTree) (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) (hh : t.ht < X.fuel) : X.leaves bl = t.lvs := by
  unfold WX.leaves; rw [← hp]; exact lleaves_ltIs (ltree X) bl t X.fuel ht hh

theorem positions_rt (X : WX) (bl : Loc) (t : RTree) (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) (hh : t.ht < X.fuel) : X.positions bl = t.pos := by
  unfold WX.positions; rw [← hp]; exact lposF_ltIs (ltree X) bl t X.fuel ht hh

theorem leafDepthOK_rt (X : WX) (bl : Loc) (h : rtOK X bl) : leafDepthOK X bl := by
  obtain ⟨t, ht, hp, hh, D, hD⟩ := h
  refine ⟨D, ?_⟩
  rw [← hp, ldepthsF_ltIs (ltree X) bl t X.fuel 0 ht hh]
  exact hD

/-- **A materialized child occurs only under its parent's position** (`nodeClean`'s parent and
child clauses; below an unmaterialized position only pages, `posNodeFree`). -/
theorem edge_mat (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (t : RTree) (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) :
    ∀ x c, t.edge x c → ∀ l r, B.nm !! c = some l → B.ns !! l = some r →
      B.nm !! x = some r.nv.parent' := by
  intro x c he l r hl hr
  obtain ⟨s, hs, hsx, hslf, hcm⟩ := he
  have hsl := ltIs_subs (ltree X) bl t s ht hs
  cases s with
  | mk p lf ws cs =>
    simp only [RTree.pid, RTree.lf, RTree.cs] at hsx hslf hcm
    subst hsx hslf
    simp only [ltIs] at hsl
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hcm
    obtain ⟨-, w, hw, hcw⟩ := ltIsL_mem _ bl ws cs hsl.2 c' hc'
    by_cases h0 : B.ib.root' = W64 0
    · exact absurd (ltree_inline_leaf X bl B hb hc h0 _ false ws hsl.1) (by simp)
    have hroot : posI X B t.pid := by
      rw [hp]
      simp only [WX.rootPid, hb, Option.map_some, Option.getD_some]
      by_cases hn : B.bv.rootNode' = null
      · right
        exact ⟨(hc.2.1 h0).2 hn, fun d _ => by rw [(hc.2.2.1 hn).2]; rfl⟩
      · left; rw [hc.2.2.2.1 hn]; simp
    have hI := posI_subs X bl B hb hc h0 t ht hroot _ hs
    rw [hcw] at hl
    exact (posI_step X bl B hb hc h0 _ hI ws hsl.1 w hw).2 l r hl hr

/-- **The root position holds the root node** (if materialized): a materialized node at the
root has no parent. -/
theorem root_mat (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B)
    (hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null)
    (l : Loc) (r : NRec) (hl : B.nm !! X.rootPid bl = some l) (hr : B.ns !! l = some r) :
    r.nv.parent' = null := by
  simp only [WX.rootPid, hb, Option.map_some, Option.getD_some] at hl
  by_cases hn : B.bv.rootNode' = null
  · rw [(hc.2.2.1 hn).2] at hl; simp at hl
  · rw [hc.2.2.2.1 hn] at hl
    cases hl
    exact hroot r hr

/-- The kind and entries of a node record (what `ltree` reads). -/
def NRec.kw (r : NRec) : Bool × List WEntry := (r.nv.isLeaf', r.ws)

/-- **`ltree` is kept off the changed positions `S`**: bucket `bl`'s record changed to `B'` with
its header, root node and node cache kept off `S`, and each node cached off `S` with its kind
and entries; the other buckets and the view kept. -/
theorem ltree_frame (X X' : WX) (bl : Loc) (B B' : BRec) (S : w64 → Prop)
    (hb : X.t.bs !! bl = some B) (hb' : X'.t.bs !! bl = some B')
    (hother : ∀ bl', bl' ≠ bl → X'.t.bs !! bl' = X.t.bs !! bl') (hv : X'.v = X.v)
    (hib : B'.ib = B.ib) (hrn : B'.bv.rootNode' = B.bv.rootNode') (hpg : B'.bv.page' = B.bv.page')
    (hipg : B'.ipg = B.ipg)
    (hnm : ∀ q, ¬ S q → B'.nm !! q = B.nm !! q)
    (hns : ∀ q l, ¬ S q → B.nm !! q = some l → (B'.ns !! l).map NRec.kw = (B.ns !! l).map NRec.kw)
    (hinl : B.ib.root' = W64 0 → (B'.ns !! B.bv.rootNode').map NRec.kw =
      (B.ns !! B.bv.rootNode').map NRec.kw) :
    ∀ bl' q, (bl' = bl → ¬ S q) → ltree X' bl' q = ltree X bl' q := by
  intro bl' q hq
  by_cases hbl : bl' = bl
  · subst hbl
    have hS := hq rfl
    have hwp : wpageAt X'.v B' q = wpageAt X.v B q := by
      simp only [wpageAt, hv, hib, hpg, hipg]
    unfold ltree
    rw [hb, hb']
    simp only
    have hres : resolve B' q = resolve B q := by
      simp only [resolve, hib, hrn, hnm q hS]
    rw [hres, hwp]
    cases hr : resolve B q with
    | none => rfl
    | some l =>
      simp only
      unfold resolve at hr
      by_cases h0 : B.ib.root' = W64 0
      · simp only [h0, ↓reduceIte] at hr
        by_cases hn : B.bv.rootNode' = null
        · simp only [hn, ↓reduceIte] at hr; cases hr
        · simp only [hn, ↓reduceIte] at hr; cases hr
          exact hinl h0
      · simp only [h0, ↓reduceIte] at hr
        exact hns q l hS hr
  · unfold ltree
    rw [hother bl' hbl, hv]

/-- The walks' fuel is kept when the view and the buckets' locations are. -/
theorem fuel_eq (X X' : WX) (hv : X'.v.pages = X.v.pages)
    (hbs : ∀ bl, (X'.t.bs !! bl).isSome = (X.t.bs !! bl).isSome) : X'.fuel = X.fuel := by
  unfold WX.fuel
  rw [hv, GMap.size_eq_length X'.t.bs X.t.bs.domList (GMap.nodup_dom_list _)
    (fun k => by rw [GMap.mem_dom_list, hbs]), ← GMap.size_eq_dom_list_length]

end rtx

end bbolt
end EtcdGrove
end Perennial
