/-
U7's (`notes/bbolt-proof-plan.md`) `wOK_nodeAdded`: materializing a page position keeps `wOK`.

The child case (a branch node's unmaterialized child) reuses U8b's `Rebalance/RblMat` (the bucket
stays clean, its keys, its nested buckets' entries); the root case (a bucket without a root node)
is proved here (`matR_*`). The entries' bound comes from the view (`viewWF_leafBound`: every
plain entry of a view's leaf page is within `bboltEntryMax`, by `rootShape`).

`nodeAdded` (`Model/WOps`) does not say three things the proof needs (premises of
`wOK_nodeAdded'`, reported to the maintainer):
- the new node's nested buckets' values are in the view or persistent (`nodeClean`'s leaf clause;
  `node.read` gives `pageWsAs pg (posSrc B)`, and `nodeAdded` keeps only the data and `wsLive`);
- the parent's `capOwn` is kept (`nodeClean`'s `capOwn = true`);
- an inline bucket's page's entries are within `bboltEntryMax` (`entriesBounded`; no `wOK` clause
  relates an inline bucket's `ipg` to its entry's value, nor bounds it).
-/
module

public import Proof.go_etcd_io.bbolt.Write.FlView
public import Proof.go_etcd_io.bbolt.Write.Bound
public import Proof.go_etcd_io.bbolt.Write.RootKeys
public import Proof.go_etcd_io.bbolt.Rebalance.RblXShape
public import Proof.go_etcd_io.bbolt.Rebalance.RblMat
public import Proof.go_etcd_io.bbolt.Rebalance.RblReady
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSObjs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section assemble
variable [GooseExts]

omit [GooseExts] in
theorem mem_ins_self {V : Type} (m : GMap Loc V) (k : Loc) (v : V) : k ∈ m.insert k v := by
  rw [GMap.mem_iff]; show ((m.insert k v) !! k).isSome = true; rw [GMap.lookup_insert]; rfl

omit [GooseExts] in
theorem mem_ins_of_mem {V : Type} {m : GMap Loc V} {k k' : Loc} (v : V) (h : k' ∈ m) :
    k' ∈ m.insert k v := by
  rw [GMap.mem_iff] at h ⊢
  show ((m.insert k v) !! k').isSome = true
  by_cases hk : k = k'
  · subst hk; rw [GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ hk]; exact h

omit [GooseExts] in
theorem mem_of_mem_ins_ne {V : Type} {m : GMap Loc V} {k k' : Loc} {v : V}
    (h : k' ∈ m.insert k v) (hne : k' ≠ k) : k' ∈ m := by
  rw [GMap.mem_iff] at h ⊢
  have h2 : ((m.insert k v) !! k').isSome = true := h
  rwa [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at h2

/-- `X` with bucket `bl`'s record `B'`, the node `l` live and registered at `(bl, pgid)`
(`nodeAdded`'s `X'`). -/
abbrev matX (X : WX) (bl l : Loc) (pgid : w64) (B' : BRec) : WX :=
  { X with t := { X.t with bs := X.t.bs.insert bl B' }, live := X.live.insert l (),
           nloc := X.nloc.insert l (bl, pgid.toNat) }

theorem matX_bs (X : WX) (bl l : Loc) (pgid : w64) (B' : BRec) (c : Loc) :
    (matX X bl l pgid B').t.bs !! c = if c = bl then some B' else X.t.bs !! c := by
  show (X.t.bs.insert bl B') !! c = _
  by_cases h : c = bl
  · subst h; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]

/-- **The leaves' root shape of a bucket grown by a fresh node** (batch 30): the other nodes'
`isLeaf` and entries kept, the new node's leaf entries of the root shape. -/
theorem leafShape_matX (X : WX) (bl l : Loc) (pgid : w64) (B B' : BRec) (r : NRec)
    (hsh : leafShape X) (hB : X.t.bs !! bl = some B) (hnew : B'.ns !! l = some r)
    (hnsN : ∀ y ry', B'.ns !! y = some ry' → y = l ∨ ∃ ry, B.ns !! y = some ry ∧
      ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws ∧ ry'.nv.pgid' = ry.nv.pgid' ∧
      ry'.key = ry.key)
    (hshape : r.nv.isLeaf' = true → ∀ w ∈ r.ws, (isBktFlag w.flags ↔ bl = X.rl)) :
    leafShape (matX X bl l pgid B') := by
  intro c C hC y ry' hy hleaf w hw
  show _ ↔ c = X.rl
  rw [matX_bs] at hC
  split at hC
  · rename_i hc
    subst hc
    cases hC
    rcases hnsN y ry' hy with rfl | ⟨ry, hry, h1, h2, -⟩
    · rw [hnew] at hy; cases hy
      exact hshape hleaf w hw
    · rw [h1] at hleaf; rw [h2] at hw
      exact hsh c B hB y ry hry hleaf w hw
  · exact hsh c C hC y ry' hy hleaf w hw

omit [GooseExts] in
theorem nm_ins_none (m : GMap w64 Loc) (c k : w64) (l : Loc) (h : (m.insert c l) !! k = none) :
    m !! k = none := by
  by_cases hk : k = c
  · subst hk; rw [GMap.lookup_insert] at h; cases h
  · rwa [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at h

theorem branchPgid_lt (pg : List w8) (i : Nat) : branchPgid pg i < 2 ^ 64 := by
  unfold branchPgid; exact BitVec.isLt _

omit [GooseExts] in
theorem w64_toNat_cast (x : w64) : W64 ((x.toNat : Nat) : Int) = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- **A new node's leaf entries of the root shape** (batch 30/35): its entries are its page's,
whose leaf flags have it. -/
theorem newNode_shape (pg : List w8) (r : NRec) (P : Prop)
    (hr9 : r.ws.map wDat = (pageWs pg).map wDat)
    (hrleaf : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag))
    (hsh : pageFlags pg = leafPageFlag → ∀ i < pageCount pg, (leafFlags pg i % 2 = bucketLeafFlag ↔ P)) :
    r.nv.isLeaf' = true → ∀ w ∈ r.ws, (isBktFlag w.flags ↔ P) := by
  intro hl w hw
  have hlf : pageFlags pg = leafPageFlag := by rw [hrleaf] at hl; exact of_decide_eq_true hl
  have hm : wDat w ∈ (pageWs pg).map wDat := by rw [← hr9]; exact List.mem_map_of_mem hw
  obtain ⟨w', hw', hd⟩ := List.mem_map.1 hm
  unfold pageWs at hw'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw'
  rw [List.mem_range] at hi
  have hf : w.flags = (pageW pg i).flags := (congrArg Prod.fst hd).symm
  rw [hf]
  simp only [pageW, if_pos hlf]
  rw [mat_isBktFlag_iff _ (mat_leafFlags_lt pg i)]
  exact hsh hlf i hi

/-- **`wOK` of a bucket grown by a fresh node** (what both cases of `wOK_nodeAdded'` give). -/
theorem wOK_matX (X : WX) (bl l : Loc) (pgid : w64) (B B' : BRec) (r : NRec)
    (hok : wOK X) (hB : X.t.bs !! bl = some B) (hlo : X.t.objs !! l = none)
    (hc' : bktClean X.v X.t.mv.pgid'.toNat bl B') (hk' : bktKeys X.v B')
    (hent : ∀ k v, entryIn X.v B k v → entryIn X.v B' k v)
    (hib : B'.ib = B.ib) (hbm : B'.bm = B.bm)
    (hrn : B'.bv.rootNode' = null → B.bv.rootNode' = null) (hipg : B'.ipg = B.ipg)
    (hnew : B'.ns !! l = some r)
    (hnsN : ∀ y ry', B'.ns !! y = some ry' → y = l ∨ ∃ ry, B.ns !! y = some ry ∧
      ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws ∧ ry'.nv.pgid' = ry.nv.pgid' ∧
      ry'.key = ry.key)
    (hnsO : ∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧
      ry'.nv.pgid' = ry.nv.pgid')
    (hpg : nodePg X.v B.ib.root' r)
    (hbnd : ∀ w ∈ r.ws, 0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax ∧
      (bl = X.rl → w.key.length ≤ maxKeySize))
    (hpid : r.nv.pgid'.toNat = pgid.toNat)
    (hshape : r.nv.isLeaf' = true → ∀ w ∈ r.ws, (isBktFlag w.flags ↔ bl = X.rl))
    (hnmS : ∀ k, B'.nm !! k = none → B.nm !! k = none)
    (hpr : r.nv.isLeaf' = false → posRoot B r.nv.pgid'.toNat) :
    wOK (matX X bl l pgid B') := by
  obtain ⟨⟨hw, ⟨hpm, hbuf, hsh, hps, hrni⟩, hpg2, htxid, hrl, hbs⟩, hkn, htp, heb, hho,
    ⟨hl1, hl2, hl3, hl4, hl5⟩, hnl, hv⟩ := hok
  have hbs' := matX_bs X bl l pgid B'
  have hcase : ∀ c C, (matX X bl l pgid B').t.bs !! c = some C →
      (c = bl ∧ C = B') ∨ (c ≠ bl ∧ X.t.bs !! c = some C) := by
    intro c C hC
    rw [hbs'] at hC
    split at hC
    · rename_i h; cases hC; exact Or.inl ⟨h, rfl⟩
    · rename_i h; exact Or.inr ⟨h, hC⟩
  have hdom : ∀ c, ((matX X bl l pgid B').t.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [hbs']; split
    · rename_i h; subst h; rw [hB]; rfl
    · rfl
  have hlB : B.ns !! l = none := Write.objs_none X.t l hlo bl B hB
  -- the objects grow
  have hobj : ∀ k, (X.t.objs !! k).isSome = true →
      ((matX X bl l pgid B').t.objs !! k).isSome = true := by
    refine objs_isSome_mono X.t (matX X bl l pgid B').t (fun k h => h) ?_
    intro c C k hC hk
    refine Or.inr ?_
    by_cases hcb : c = bl
    · subst hcb; rw [hB] at hC; cases hC
      obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 hk
      obtain ⟨ry', h1, -⟩ := hnsO k r0 hr0
      exact ⟨c, B', by rw [hbs', if_pos rfl], by rw [h1]; rfl⟩
    · exact ⟨c, C, by rw [hbs', if_neg hcb]; exact hC, hk⟩
  have hlobj : ((matX X bl l pgid B').t.objs !! l).isSome = true := by
    rw [objs_isSome]
    exact Or.inr ⟨bl, B', by rw [hbs', if_pos rfl], by rw [hnew]; rfl⟩
  have hldead : X.t.dead !! l = none := by
    cases h : X.t.dead !! l with
    | none => rfl
    | some o =>
      have : (X.t.objs !! l).isSome = true := by
        rw [objs_isSome]; exact Or.inl (by rw [h]; rfl)
      rw [hlo] at this; cases this
  have hps' : posShape (matX X bl l pgid B') := by
    intro c C hC c0 p pg0 hpos hown hpg0 hleaf i hi
    show (_ ↔ c = X.rl) ∧ _ ∧ (c = X.rl → _) ∧ (c = X.rl → _)
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · rcases hpos with ⟨hrn', h0', rfl⟩ | ⟨y, j, ⟨ry', w, hy, hyl, hw, hwp, hnm'⟩, hlt⟩
      · exact hps c B hB _ p pg0 (Or.inl ⟨hrn hrn', by rw [← hib]; exact h0', by rw [hib]⟩)
          hown hpg0 hleaf i hi
      · rcases hnsN y ry' hy with rfl | ⟨ry, hry, a1, a2, -⟩
        · rw [hnew] at hy; cases hy
          obtain ⟨-, hbr⟩ := hpg
          obtain ⟨-, pgr, hpgr, hfb, hlen, hch⟩ := hbr hyl
          have hwj := hch j w hw
          have hj : j < pageCount pgr := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hw).1
          have hc0 : c0 = branchPgid pgr j := by
            have h1 := congrArg BitVec.toNat (hwp.symm.trans hwj)
            have h2 := branchPgid_lt pgr j
            simp only [BitVec.toNat_ofInt] at h1
            omega
          have hown' : ownHas X.v.pages r.nv.pgid'.toNat p :=
            ownHas.child _ pgr j p hpgr hfb hj (hc0 ▸ hown)
          exact hps c B hB _ p pg0 (hpr hyl) hown' hpg0 hleaf i hi
        · exact hps c B hB _ p pg0
            (Or.inr ⟨y, j, ⟨ry, w, hry, by rw [← a1]; exact hyl, by rw [← a2]; exact hw, hwp,
              hnmS _ hnm'⟩, hlt⟩) hown hpg0 hleaf i hi
    · exact hps c C hC0 c0 p pg0 hpos hown hpg0 hleaf i hi
  have hrni' : rootNotInline (matX X bl l pgid B') := by
    intro C hC
    rcases hcase X.rl C hC with ⟨h, rfl⟩ | ⟨-, hC0⟩
    · rw [hib]; exact hrni B (by rw [h]; exact hB)
    · exact hrni C hC0
  refine ⟨⟨hw, ⟨hpm, hbuf, leafShape_matX X bl l pgid B B' r hsh hB hnew hnsN hshape,
    hps', hrni'⟩, hpg2, htxid,
    by rw [hdom]; exact hrl, fun c C hC => ?_⟩, fun c C hC => ?_,
    ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hv⟩
  · -- txClean
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · refine ⟨hc', fun name c' hn => ?_⟩
      rw [hbm] at hn; rw [hdom]; exact (hbs c B hB).2 name c' hn
    · exact ⟨(hbs c C hC0).1, fun name c' hn => by rw [hdom]; exact (hbs c C hC0).2 name c' hn⟩
  · -- keys and nested buckets
    have hnest : ∀ C0, X.t.bs !! c = some C0 → (∀ k v, entryIn X.v C0 k v → entryIn X.v C k v) →
        C.bm = C0.bm → bktNested X.v (matX X bl l pgid B').t C := by
      intro C0 hC0 he hbm0 k c' hk
      rw [hbm0] at hk
      obtain ⟨C2, v, hC2, hin, h16, hinl, hroot, hrn2, hipg2, hbo2, htk2⟩ := (hkn c C0 hC0).2 k c' hk
      by_cases hcb : c' = bl
      · subst hcb
        rw [hB] at hC2; cases hC2
        exact ⟨B', v, by rw [hbs', if_pos rfl], he k v hin, h16, hinl, by rw [hib]; exact hroot,
          fun h0 => by rw [hib]; exact hrn2 (hrn h0),
          fun h0 h1 => by rw [hipg]; exact hipg2 (by rw [← hib]; exact h0) (hrn h1), hbo2, htk2⟩
      · exact ⟨C2, v, by rw [hbs', if_neg hcb]; exact hC2, he k v hin, h16, hinl, hroot, hrn2,
          hipg2, hbo2, htk2⟩
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · exact ⟨hk', hnest B hB hent hbm⟩
    · exact ⟨(hkn c C hC0).1, hnest C hC0 (fun _ _ h => h) rfl⟩
  · -- nodes' pages
    intro c C hC y ry hy
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · rw [hib]
      rcases hnsN y ry hy with rfl | ⟨ry0, hry0, a1, a2, a3, a4⟩
      · rw [hnew] at hy; cases hy; exact hpg
      · have := htp c B hB y ry0 hry0
        unfold nodePg at this ⊢
        rw [a1, a2, a3, a4]; exact this
    · exact htp c C hC0 y ry hy
  · -- entries bounded
    intro c C hC y ry hy
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · rcases hnsN y ry hy with rfl | ⟨ry0, hry0, a1, a2, -⟩
      · rw [hnew] at hy; cases hy; exact hbnd
      · rw [a2]; exact heb c B hB y ry0 hry0
    · exact heb c C hC0 y ry hy
  · -- handles
    intro b nm hb
    exact bobjs_isSome_mono X.t (matX X bl l pgid B').t (fun k h => h)
      (fun c h => by rw [hdom]; exact h) b (hho b nm hb)
  · -- live: the root
    exact hl1
  · intro k hk
    by_cases hkl : k = l
    · subst hkl; exact hlobj
    · exact hobj k (hl2 k (mem_of_mem_ins_ne hk hkl))
  · intro c C hC
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · exact hl3 c B hB
    · exact hl3 c C hC0
  · intro c C y ry hC hy
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · rcases hnsN y ry hy with rfl | ⟨ry0, hry0, -⟩
      · exact mem_ins_self _ _ _
      · exact mem_ins_of_mem () (hl4 c B y ry0 hB hry0)
    · exact mem_ins_of_mem () (hl4 c C y ry hC0 hy)
  · intro k hk hkl
    by_cases he : k = l
    · subst he; rw [hldead] at hk; cases hk
    · exact hl5 k hk (mem_of_mem_ins_ne hkl he)
  · -- the registry
    intro n b p hn hlive
    by_cases hnl' : n = l
    · subst hnl'
      have : (bl, pgid.toNat) = (b, p) := by
        have h2 : (X.nloc.insert n (bl, pgid.toNat)) !! n = some (b, p) := hn
        rw [GMap.lookup_insert] at h2; exact Option.some.inj h2
      cases this
      exact ⟨B', r, by rw [hbs', if_pos rfl], hnew, hpid⟩
    · have hn0 : X.nloc !! n = some (b, p) := by
        have h2 : (X.nloc.insert l (bl, pgid.toNat)) !! n = some (b, p) := hn
        rwa [GMap.lookup_insert_ne _ _ (Ne.symm hnl')] at h2
      obtain ⟨C, ry, hC, hry, hp⟩ := hnl n b p hn0 (mem_of_mem_ins_ne hlive hnl')
      by_cases hbb : b = bl
      · subst hbb; rw [hB] at hC; cases hC
        obtain ⟨ry', h1, h2⟩ := hnsO n ry hry
        exact ⟨B', ry', by rw [hbs', if_pos rfl], h1, by rw [h2]; exact hp⟩
      · exact ⟨C, ry, by rw [hbs', if_neg hbb]; exact hC, hry, hp⟩

end assemble

/-! ## The root case: a bucket without a root node gets one -/

section root
variable [GooseExts]

/-- The bucket after its root page `c` was materialized as its root node `l` (record `r`). -/
def matRBkt (B : BRec) (c : w64) (l : Loc) (r : NRec) : BRec :=
  { B with nm := B.nm.insert c l, ns := B.ns.insert l r, bv := { B.bv with rootNode' := l } }

theorem matR_ns (B : BRec) (c : w64) (l : Loc) (r : NRec) (hns : B.ns = ∅) (y : Loc) :
    (matRBkt B c l r).ns !! y = if y = l then some r else none := by
  show (B.ns.insert l r) !! y = _
  rw [hns]
  by_cases h : y = l
  · subst h; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]; rfl

theorem matR_nm (B : BRec) (c : w64) (l : Loc) (r : NRec) (hnm : B.nm = ∅) (k : w64) :
    (matRBkt B c l r).nm !! k = if k = c then some l else none := by
  show (B.nm.insert c l) !! k = _
  rw [hnm]
  by_cases h : k = c
  · subst h; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]; rfl

variable (W : View) (hwm : Nat) (bl : Loc) (B : BRec) (hv : pagesStrict W.pages)
    (hc : bktClean W hwm bl B) (hrn0 : B.bv.rootNode' = null) (l : Loc) (hl : l ≠ null)
    (pg : List w8) (r : NRec) (hr : matNew bl null pg r)
    (hpt : pageTreeWF W.pages hwm pg pg.length) (hgood : pageGood pg)
    (hcid : (pageHdr pg).id' = B.ib.root')
    (hfile : B.ib.root' ≠ W64 0 → W.pages !! B.ib.root'.toNat = some pg)
    (hinl : B.ib.root' = W64 0 → pageFlags pg = leafPageFlag ∧
      ∀ j < pageCount pg, leafFlags pg j % 2 = 0)
include hv hc hrn0 hl hr hpt hgood hcid hfile hinl

set_option linter.unusedVariables false in
/-- The new root node's children are not materialized, and are none of its page. -/
theorem matR_free : ∀ j < pageCount pg, pageFlags pg = branchPageFlag →
    B.ib.root' ≠ W64 0 ∧ W.pages !! B.ib.root'.toNat = some pg ∧
    treeWF W.pages hwm (branchPgid pg j) ∧
    (matRBkt B B.ib.root' l r).nm !! W64 (branchPgid pg j : Int) = none ∧
    ¬ treeHas W.pages (branchPgid pg j) B.ib.root'.toNat := by
  intro j hj hb
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; rw [(hinl h0).1] at hb; exact absurd hb leaf_ne_branch
  have hpg := hfile hroot
  rcases mat_kind hpt with ⟨h, -⟩ | ⟨-, -, hbk⟩
  · rw [h] at hb; exact absurd hb leaf_ne_branch
  have hnot := (hv.2.1 _ pg hpg hb).2 j hj
  refine ⟨hroot, hpg, hbk j hj, ?_, hnot⟩
  rw [matR_nm _ _ _ _ (hc.2.2.1 hrn0).2, if_neg]
  intro he
  rw [mat_W64_eq_iff _ _ (mat_branchPgid_lt pg j)] at he
  cases hbk j hj with
  | page _ pgj _ _ hpgj _ _ _ => exact hnot (he ▸ treeHas.root _ pgj hpgj)

set_option linter.unusedVariables false in
/-- The page positions of the new root node: its children. -/
theorem matR_pos : ∀ x j c', pagePosAt (matRBkt B B.ib.root' l r) x j c' →
    x = l ∧ pageFlags pg = branchPageFlag ∧ j < pageCount pg ∧
      c' = W64 (branchPgid pg j : Int) := by
  intro x j c' ⟨ry, wy, hy, hyleaf, hwy, hwyp, _⟩
  rw [matR_ns _ _ _ _ (hc.2.2.1 hrn0).1] at hy
  split at hy
  · rename_i hxl
    cases hy
    have hnleaf : pageFlags pg ≠ leafPageFlag := by
      intro h; rw [hr.2.2.2.1, h] at hyleaf; simp at hyleaf
    have hbr' : pageFlags pg = branchPageFlag := by
      rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hnleaf
      · exact h
    obtain ⟨hj, hd⟩ := mat_at hr.2.2.2.2.2.2.2.2.1 j wy hwy
    refine ⟨hxl, hbr', hj, ?_⟩
    rw [← hwyp, (mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]
  · cases hy

/-- The keys of a page read by a writer are non-empty. -/
theorem matR_nodes : ∀ j < pageCount pg, 0 < (pageKey pg j).length := by
  intro j hj
  rcases mat_kind hpt with ⟨hf, hwf, -⟩ | ⟨hf, hwf, -⟩
  · have hk := (hgood.1 hf j hj).1
    have hb := (hwf.2.2.1 j hj).1
    rw [mat_pageKey_leaf pg j hf]; unfold leafKey
    rw [mat_bytesAt_length _ _ _ (by omega)]; exact hk
  · have hk := hgood.2 hf j hj
    have hb := (hwf.2.2.2.1 j hj).1
    rw [mat_pageKey_branch pg j hf]; unfold branchKey
    rw [mat_bytesAt_length _ _ _ (by omega)]; exact hk

/-- **Materializing a bucket's root page keeps it clean.** -/
theorem matR_clean (hx1 : r.ins.length = r.ws.length) (hx2 : r.nv.key' = slice.nil ↔ r.ws = [])
    (hx3 : ∀ w ∈ r.ws, isBktFlag w.flags → w.vs = Src.view ∨ w.vs = Src.own DFrac.discard)
    (hni : leafInl pg) (hnest : matNest W.pages pg) :
    bktClean W hwm bl (matRBkt B B.ib.root' l r) := by
  have hfree := matR_free W hwm bl B hv hc hrn0 l hl pg r hr hpt hgood hcid hfile hinl
  have hposR := matR_pos W hwm bl B hv hc hrn0 l hl pg r hr hpt hgood hcid hfile hinl
  have hnodes := matR_nodes W hwm bl B hv hc hrn0 l hl pg r hr hpt hgood hcid hfile hinl
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩ := hr
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11⟩ := hc
  have hns0 := (hc3 hrn0).1
  have hnm0 := (hc3 hrn0).2
  have hns' := matR_ns B B.ib.root' l r hns0
  have hnm' := matR_nm B B.ib.root' l r hnm0
  have hrid : r.nv.pgid' = B.ib.root' := hr3.trans hcid
  have hkind := mat_kind hpt
  have huniq := hv.2
  refine ⟨fun _ h => absurd h hl, fun h => ⟨(hc2 h).1, fun h' => absurd h' hl⟩,
    fun h => absurd h hl, fun _ => ?_, ?_, hc6, ?_, ?_, ?_, ?_⟩
  · show (matRBkt B B.ib.root' l r).nm !! B.ib.root' = some l
    rw [hnm', if_pos rfl]
  · intro k l' hk
    rw [hnm'] at hk
    split at hk
    · rename_i hkc
      cases hk
      exact ⟨hl, r, by rw [hns', if_pos rfl], by rw [hrid, hkc]⟩
    · cases hk
  · intro h0 y ry hy
    rw [hns'] at hy
    split at hy
    · cases hy; rw [hr4]; simp [(hinl h0).1]
    · cases hy
  · intro y ry hy
    rw [hns'] at hy
    split at hy
    · rename_i hyl
      cases hy
      have hsorted : wsSorted r.ws := by
        intro a b hab hb
        rw [mat_len hr9] at hb
        rw [mat_wKey hr9, mat_wKey hr9, mat_wKey_page pg a (by omega), mat_wKey_page pg b hb]
        rcases hkind with ⟨hf, hwf, -⟩ | ⟨hf, hwf, -⟩
        · rw [mat_pageKey_leaf pg a hf, mat_pageKey_leaf pg b hf]
          exact hwf.2.2.2 a b hab hb
        · rw [mat_pageKey_branch pg a hf, mat_pageKey_branch pg b hf]
          exact hwf.2.2.2.2 a b hab hb
      have hkeys : ∀ x ∈ r.ws, 0 < x.key.length := by
        intro x hx
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
        rw [(mat_wDat_eq hd).2.2.1, mat_pageW_key]; exact hnodes j hjc
      refine ⟨hr1, hr8, hx1, hsorted, hkeys, hr10, hr6, ?_, fun h0 => by rw [hrid]; exact h0,
        fun h0 => by rw [hrid]; exact (hc2 h0).2 hrn0, ?_, ?_, ?_, fun _ => by rw [hyl]; rfl,
        fun h => absurd hr2 h, by rw [hr7]; exact List.nodup_nil,
        fun z hz => by rw [hr7] at hz; cases hz⟩
      · show (matRBkt B B.ib.root' l r).nm !! r.nv.pgid' = some y
        rw [hrid, hnm', if_pos rfl, hyl]
      · by_cases hws : r.ws = []
        · exact Or.inl (hx2.2 hws)
        · refine Or.inr ⟨?_, hr12⟩
          have hcnt : 0 < pageCount pg := by
            rw [← mat_len hr9]; exact List.length_pos_iff.2 hws
          rw [hr11, mat_wKey hr9, mat_wKey_page pg 0 hcnt]; exact hnodes 0 hcnt
      · intro hleaf x hx hbk
        have hfl : pageFlags pg = leafPageFlag := by rw [hr4] at hleaf; simpa using hleaf
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
        obtain ⟨e1, -, -, e4⟩ := mat_wDat_eq hd
        obtain ⟨f1, -, -, f4⟩ := mat_pageW_leaf pg j hfl
        have hbk' : leafFlags pg j % 2 = bucketLeafFlag := by
          rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)] at hbk; exact hbk
        rcases hkind with ⟨-, -, hbw⟩ | ⟨hb, -, -⟩
        · refine ⟨fun _ => ?_, hx3 x hx hbk⟩
          rw [e4, f4]
          -- the nested-plainness clause, from the view page (`matNest`)
          exact ⟨hbw j hjc hbk', fun h0 => ⟨(hgood.1 hfl j hjc).2 hbk' h0, hni hfl j hjc hbk' h0⟩,
            fun _ bpg hb => hnest hfl j hjc hbk' bpg hb⟩
        · rw [hb] at hfl; exact absurd hfl mat_branch_ne_leaf
      · intro hleaf
        have hnleaf : pageFlags pg ≠ leafPageFlag := by
          intro h; rw [hr4, h] at hleaf; simp at hleaf
        rcases hkind with ⟨h, -⟩ | ⟨hb, hbw, hbk⟩
        · exact absurd h hnleaf
        have hpg := (hfree 0 hbw.1 hb).2.1
        refine ⟨by rw [mat_len hr9]; exact hbw.1, ?_, ?_⟩
        · rw [mat_pgids hr9]
          have hmap : (pageWs pg).map WEntry.pgid =
              (List.range (pageCount pg)).map fun j => W64 (branchPgid pg j : Int) := by
            unfold pageWs; rw [List.map_map]; congr 1; funext j
            exact (mat_pageW_branch pg j hnleaf).1
          rw [hmap]
          refine mat_nodup_map_on _ _ List.nodup_range ?_
          intro a ha b hb' hab
          have ha' := List.mem_range.1 ha
          have hb'' := List.mem_range.1 hb'
          refine Classical.byContradiction fun hne => ?_
          have hax : branchPgid pg a = branchPgid pg b := by
            have := congrArg BitVec.toNat hab
            rwa [toNat_W64_of_lt _ (mat_branchPgid_lt _ _),
              toNat_W64_of_lt _ (mat_branchPgid_lt _ _)] at this
          cases hbk a ha' with
          | page _ pga _ _ hpga _ _ _ =>
            exact (huniq.1 _ pg hpg hb).1 a b ha' hb'' hne _ (treeHas.root _ pga hpga)
              (hax ▸ treeHas.root _ pga hpga)
        · intro x hx
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
          obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
          have hpj : x.pgid = W64 (branchPgid pg j : Int) := by
            rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]
          rw [hpj]
          have hjnone := (hfree j hjc hb).2.2.2.1
          refine ⟨by rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)]; exact (hbw.2.2.2.1 j hjc).2.2,
            ?_, ?_⟩
          · intro l' hl'; rw [hjnone] at hl'; cases hl'
          · intro _; rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)]; exact hbk j hjc
    · cases hy
  · -- positions disjoint
    intro x1 j1 c1 x2 j2 c2 hP1 hP2 hne d hd1 hd2
    obtain ⟨rfl, hb, hj1, rfl⟩ := hposR x1 j1 c1 hP1
    obtain ⟨hx2, -, hj2, rfl⟩ := hposR x2 j2 c2 hP2
    subst hx2
    have hjne : j1 ≠ j2 := by intro h; exact hne (by rw [h])
    rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)] at hd1
    rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)] at hd2
    exact (huniq.1 _ pg (hfree j1 hj1 hb).2.1 hb).1 j1 j2 hj1 hj2 hjne d hd1 hd2
  · -- positions node-free (and, batch 37, the cached children: `bm` unchanged)
    refine ⟨fun x j c' hP d hd => ?_, hc11⟩
    obtain ⟨-, hb, hj, rfl⟩ := hposR x j c' hP
    obtain ⟨-, -, hwf, -, hnot⟩ := hfree j hj hb
    rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)] at hd
    rw [hnm']
    split
    · rename_i hdc
      rw [mat_W64_eq_iff _ _ (mat_has_lt hwf hd)] at hdc
      subst hdc
      exact absurd hd hnot
    · rfl

/-- **Materializing a bucket's root page keeps its keys** (the root node's bounds are none). -/
theorem matR_keys (htk : B.ib.root' ≠ W64 0 → treeKeys W.pages B.ib.root'.toNat none none) :
    bktKeys W (matRBkt B B.ib.root' l r) := by
  have hfree := matR_free W hwm bl B hv hc hrn0 l hl pg r hr hpt hgood hcid hfile hinl
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩ := hr
  have hns' := matR_ns B B.ib.root' l r (hc.2.2.1 hrn0).1
  refine ⟨fun _ => (none, none), fun h => absurd h hl, fun r0 h0 => ?_, fun y ry hy => ?_⟩
  · change (matRBkt B B.ib.root' l r).ns !! l = some r0 at h0
    rw [hns', if_pos rfl] at h0; cases h0; exact hr2
  rw [hns'] at hy
  split at hy
  rotate_left
  · cases hy
  cases hy
  refine ⟨fun _ _ => ⟨fun _ h => (by simp at h), fun _ h => (by simp at h)⟩, fun _ => rfl,
    fun h => absurd hr2 h, fun hlf => ?_, fun _ _ h => absurd hr2 h, fun hlf x hxm hbk h0 _ => ?_⟩
  · have hnleaf : pageFlags pg ≠ leafPageFlag := by
      intro h; rw [hr4, h] at hlf; simp at hlf
    have hb : pageFlags pg = branchPageFlag := by
      rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hnleaf
      · exact h
    have hroot : B.ib.root' ≠ W64 0 := by
      intro h0; exact hnleaf (hinl h0).1
    have hpg := hfile hroot
    have htk' := htk hroot
    cases htk' with
    | leaf _ pg' _ _ hpg' hl' _ _ => rw [hpg] at hpg'; cases hpg'; exact absurd hl' hnleaf
    | branch _ pg' _ _ kindN hpg' hbr' h2 _ hch hsub =>
      rw [hpg] at hpg'; cases hpg'
      refine ⟨by rw [mat_len hr9]; exact h2, decide (kindN = leafPageFlag), fun j x hj => ?_⟩
      obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
      obtain ⟨cpg, hcpg, hcc, hcf, hck⟩ := hch j hjc
      have hpj : x.pgid = W64 (branchPgid pg j : Int) := by
        rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]
      have hnm0 := (hfree j hjc hbr').2.2.2.1
      rw [← hpj] at hnm0
      refine ⟨fun l' hl' => (by rw [hnm0] at hl'; cases hl'), fun _ => ⟨cpg, ?_, hcc,
        by rw [hcf], ?_, ?_⟩⟩
      · rw [hpj, toNat_W64_of_lt _ (mat_branchPgid_lt pg j)]; exact hcpg
      · rw [hck, (mat_wDat_eq hd).2.2.1, (mat_pageW_branch pg j hnleaf).2]
      · rw [hpj, toNat_W64_of_lt _ (mat_branchPgid_lt pg j), mat_wEntryBnd hr9,
          mat_entryBnd_page _ pg j hjc hnleaf]
        exact hsub j hjc
  · have hfl : pageFlags pg = leafPageFlag := by rw [hr4] at hlf; simpa using hlf
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hxm
    obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
    obtain ⟨e1, e2, -, e4⟩ := mat_wDat_eq hd
    obtain ⟨f1, f2, -, f4⟩ := mat_pageW_leaf pg j hfl
    rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)] at hbk
    rw [e4, f4] at h0 ⊢
    by_cases hroot : B.ib.root' = W64 0
    · have := (hinl hroot).2 j hjc; rw [hbk] at this; unfold bucketLeafFlag at this; omega
    have hpg := hfile hroot
    cases htk hroot with
    | leaf _ pg' _ _ hpg' _ _ hbkt =>
      rw [hpg] at hpg'; cases hpg'
      exact hbkt j hjc hbk h0
    | branch _ pg' _ _ _ hpg' hbr' _ _ _ _ =>
      rw [hpg] at hpg'; cases hpg'
      rw [hfl] at hbr'; exact absurd hbr'.symm mat_branch_ne_leaf

set_option linter.unusedVariables false in
/-- An entry on a page of the bucket's root position: in the new root node, or on a page of one
of its children's positions. -/
theorem matR_entryIn (k v : List w8) (h : entryIn W B k v) :
    entryIn W (matRBkt B B.ib.root' l r) k v := by
  have hfree := matR_free W hwm bl B hv hc hrn0 l hl pg r hr hpt hgood hcid hfile hinl
  have hns0 := (hc.2.2.1 hrn0).1
  have hns' := matR_ns B B.ib.root' l r hns0
  have hrl : (matRBkt B B.ib.root' l r).ns !! l = some r := by rw [hns', if_pos rfl]
  have hr4 := hr.2.2.2.1
  have hr9 := hr.2.2.2.2.2.2.2.2.1
  rcases h with ⟨y, ry, w', hy, -⟩ | ⟨c', q, pgq, j, hpos', hown, hpq, hlq, hj, hkq, hfq, hvq⟩
  · rw [hns0] at hy; cases hy
  rcases hpos' with ⟨-, hroot, rfl⟩ | ⟨y, j0, ⟨ry, -, hy, -⟩, -⟩
  rotate_left
  · rw [hns0] at hy; cases hy
  have hpg := hfile hroot
  rcases mat_ownHas_cases pg hpg hown with rfl | ⟨hb, i', hi', hown'⟩
  · rw [hpg] at hpq; cases hpq
    obtain ⟨x, hx, hd⟩ := mat_at' hr9 j hj
    obtain ⟨e1, -, e3, e4⟩ := mat_wDat_eq hd
    obtain ⟨f1, -, f3, f4⟩ := mat_pageW_leaf _ j hlq
    refine Or.inl ⟨l, r, x, hrl, by rw [hr4]; simp [hlq], List.mem_of_getElem? hx,
      by rw [e3, f3]; exact hkq, ?_, by rw [e4, f4]; exact hvq⟩
    rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt _ j)]; exact hfq
  · have hnl : pageFlags pg ≠ leafPageFlag := by rw [hb]; exact mat_branch_ne_leaf
    obtain ⟨x, hx, hd⟩ := mat_at' hr9 i' hi'
    refine Or.inr ⟨branchPgid pg i', q, pgq, j, Or.inr ⟨l, i', ⟨r, x, hrl,
      by rw [hr4]; simp [hnl], hx, by rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg i' hnl).1],
      (hfree i' hi' hb).2.2.2.1⟩, mat_branchPgid_lt pg i'⟩, hown', hpq, hlq, hj, hkq, hfq, hvq⟩

end root

/-! ## The new node's pages and entries -/

section newnode
variable [GooseExts]

/-- The keys of a page a writer reads are non-empty. -/
theorem pageKeys_pos (P : Pages) (hwm : Nat) (pg : List w8) (hpt : pageTreeWF P hwm pg pg.length)
    (hgood : pageGood pg) : ∀ j < pageCount pg, 0 < (pageKey pg j).length := by
  intro j hj
  rcases mat_kind hpt with ⟨hf, hwf, -⟩ | ⟨hf, hwf, -⟩
  · have hk := (hgood.1 hf j hj).1
    have hb := (hwf.2.2.1 j hj).1
    rw [mat_pageKey_leaf pg j hf]; unfold leafKey
    rw [mat_bytesAt_length _ _ _ (by omega)]; exact hk
  · have hk := hgood.2 hf j hj
    have hb := (hwf.2.2.2.1 j hj).1
    rw [mat_pageKey_branch pg j hf]; unfold branchKey
    rw [mat_bytesAt_length _ _ _ (by omega)]; exact hk

/-- The new node's pages (`txPg`): its page is the view's (a file bucket's). -/
theorem newNodePg (v : View) (root : w64) (pg : List w8) (r : NRec)
    (hr9 : r.ws.map wDat = (pageWs pg).map wDat)
    (hr4 : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag)) (hkey : r.key = wKey r.ws 0)
    (hkind : pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag)
    (hfile : root ≠ W64 0 → v.pages !! r.nv.pgid'.toNat = some pg)
    (hbr : pageFlags pg = branchPageFlag → root ≠ W64 0) : nodePg v root r := by
  refine ⟨fun hlf => ?_, fun hlf => ?_⟩
  · have hfl : pageFlags pg = leafPageFlag := by rw [hr4] at hlf; simpa using hlf
    refine ⟨fun x hx => ?_, fun h0 => ⟨pg, hfile h0, hfl⟩⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨-, hd⟩ := mat_at hr9 j x hj
    rw [(mat_wDat_eq hd).2.1, (mat_pageW_leaf pg j hfl).2.1]
  · have hnleaf : pageFlags pg ≠ leafPageFlag := by
      intro h; rw [hr4, h] at hlf; simp at hlf
    have hb : pageFlags pg = branchPageFlag := by
      rcases hkind with h | h
      · exact absurd h hnleaf
      · exact h
    refine ⟨⟨hkey, fun pg' hpg' => ?_⟩, pg, hfile (hbr hb), hb, mat_len hr9, fun j x hj => ?_⟩
    · -- U6y's F3: the keys are the page's
      rw [hfile (hbr hb)] at hpg'; cases hpg'
      have hk := congrArg (List.map fun d : w32 × w64 × List w8 × List w8 => d.2.2.1) hr9
      simp only [List.map_map, Function.comp_def, wDat] at hk
      rw [hk]; unfold pageWs; rw [List.map_map]
      exact List.map_congr_left (fun j _ => mat_pageW_key pg j)
    obtain ⟨-, hd⟩ := mat_at hr9 j x hj
    rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]

omit [GooseExts] in
theorem bytesAt_length_le (pg : List w8) (off n : Nat) : (bytesAt pg off n).length ≤ n := by
  unfold bytesAt; exact List.length_take_le _ _

/-- The new node's entries are bounded (`entriesBounded`); (item 3, batch 43.4) under `P` (the
bucket is the root bucket) its keys at most `MaxKeySize`, given the page's (`hroot`). -/
theorem newNodeBnd (pg : List w8) (r : NRec) (hr9 : r.ws.map wDat = (pageWs pg).map wDat)
    (hr4 : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag))
    (hnodes : ∀ j < pageCount pg, 0 < (pageKey pg j).length) (hb : leafBnd pg)
    (hbk : pageFlags pg = leafPageFlag → ∀ j < pageCount pg, leafFlags pg j % 2 = bucketLeafFlag →
      leafKsize pg j + leafVsize pg j ≤ bboltEntryMax)
    (hkb : pageFlags pg ≠ leafPageFlag → ∀ j < pageCount pg, (pageKey pg j).length ≤ bboltEntryMax)
    {P : Prop}
    (hroot : P → ∀ j < pageCount pg, (pageKey pg j).length ≤ maxKeySize) :
    ∀ w ∈ r.ws, 0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax ∧
      (P → w.key.length ≤ maxKeySize) := by
  intro x hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
  obtain ⟨e1, -, e3, e4⟩ := mat_wDat_eq hd
  refine ⟨by rw [e3, mat_pageW_key]; exact hnodes j hjc, ?_,
    fun hP => by rw [e3, mat_pageW_key]; exact hroot hP j hjc⟩
  -- batch 37: `entriesBounded` covers every entry; a branch key (`hkb`, exact branch keys) and a
  -- bucket entry (`hbk`, `posShape`'s entry bound) are bounded too
  by_cases hlf' : r.nv.isLeaf' = false
  · have hnl : pageFlags pg ≠ leafPageFlag := by
      intro h; rw [hr4, h] at hlf'; simp at hlf'
    have hv : (pageW pg j).value = [] := by unfold pageW; rw [if_neg hnl]
    rw [e3, e4, mat_pageW_key, hv, List.length_nil, Nat.add_zero]
    exact hkb hnl j hjc
  have hlf : r.nv.isLeaf' = true := by simpa using hlf'
  have hfl : pageFlags pg = leafPageFlag := by rw [hr4] at hlf; simpa using hlf
  by_cases hnb : isBktFlag x.flags
  · obtain ⟨f1, -, f3, f4⟩ := mat_pageW_leaf pg j hfl
    rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)] at hnb
    have := hbk hfl j hjc hnb
    rw [e3, f3, e4, f4]
    unfold leafKey leafValue
    have := bytesAt_length_le pg (elemOff j + leafPos pg j) (leafKsize pg j)
    have := bytesAt_length_le pg (elemOff j + leafPos pg j + leafKsize pg j) (leafVsize pg j)
    omega
  obtain ⟨f1, -, f3, f4⟩ := mat_pageW_leaf pg j hfl
  rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)] at hnb
  have h0 : leafFlags pg j % 2 = 0 := by unfold bucketLeafFlag at hnb; omega
  have := hb hfl j hjc h0
  rw [e3, f3, e4, f4]
  unfold leafKey leafValue
  have := bytesAt_length_le pg (elemOff j + leafPos pg j) (leafKsize pg j)
  have := bytesAt_length_le pg (elemOff j + leafPos pg j + leafKsize pg j) (leafVsize pg j)
  omega

end newnode

/-! ## The child case's exact keys (without `rebalance`'s `brFirst`) -/

section childkeys
variable [GooseExts]
variable (W : View) (hwm : Nat) (bl : Loc) (B : BRec) (hv : pagesStrict W.pages)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (l : Loc) (hfresh : B.ns !! l = none) (hl : l ≠ null)
    (pg : List w8) (hpg : W.pages !! w.pgid.toNat = some pg) (r rp' : NRec)
    (hr : matNew bl nl pg r) (hp' : matParent rp rp' l)
include hv hc hrp hbr hw hnone hfresh hl hpg hr hp'

/-- **Materializing the page position `w.pgid` (entry `i` of the branch node `nl`) keeps the
bucket's exact keys**, the new node's bounds its entry's (`wEntryBnd (bnd nl) rp.ws i`). The
direct form of U8b's `rblKeys_addChild`, needing no `brFirst` (so no `txPg`). -/
theorem bktKeys_addChild (hx : matExtra r) (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : bktKeysB W B bnd) :
    bktKeysB W (matBkt B w.pgid nl l rp' r)
      (fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) := by
  obtain ⟨hroot, hrn, hnl, hlnl, hpgc, hcid, hwfc, hpt, hpos⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnsB := mat_nsB W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hold' := mat_old W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hfree := mat_free W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩ := hr
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hp'
  obtain ⟨hk1, hk2, hk3⟩ := hk
  have hns' := mat_ns B w.pgid nl l rp' r
  have hnm' := mat_nm B w.pgid nl l rp' r
  obtain ⟨-, -, -, hrpk3, -, -⟩ := hk3 nl rp hrp
  obtain ⟨-, kind, hkd⟩ := hrpk3 hbr
  obtain ⟨pg', hpg', hcnt, hkind0, hkey0, htk⟩ := (hkd i w hw).2 hnone
  rw [hpg] at hpg'; cases hpg'
  have hold : ∀ x, (B.ns !! x).isSome → x ≠ l := by
    intro x hx he; rw [he, hfresh] at hx; cases hx
  have hpar : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null →
      (B.ns !! ry.nv.parent').isSome := by
    intro y ry hy hp
    obtain ⟨rq, hrq, -⟩ := ncol_par (hc.2.2.2.2.2.2.2.1 y ry hy) hp
    rw [hrq]; rfl
  refine ⟨fun h => hk1 h, ?_, ?_⟩
  · intro r0 h0
    have hrs := hc.2.2.2.1 hrn
    obtain ⟨-, rr, hrr, -⟩ := hc.2.2.2.2.1 _ _ hrs
    change (matBkt B w.pgid nl l rp' r).ns !! B.bv.rootNode' = some r0 at h0
    obtain ⟨ry0, hry0, hpar0, -⟩ := hold' _ r0 h0 (hold _ (by rw [hrr]; rfl))
    rw [hpar0]; exact hk2 ry0 hry0
  intro y ry hy
  by_cases hyl : y = l
  · rw [hns', if_pos hyl] at hy; cases hy
    have hnlb : (if nl = l then wEntryBnd (bnd nl) rp.ws i else bnd nl) = bnd nl := by
      rw [if_neg (Ne.symm hlnl)]
    have hybF : (fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) y =
        wEntryBnd (bnd nl) rp.ws i := by simp only [if_pos hyl]
    have hk0 : r.key = w.key := by
      rw [hr11, mat_wKey hr9, mat_wKey_page pg 0 hcnt]; exact hkey0
    have htk' := mat_treeKeys_key _ _ _ _ pg htk hpg
    refine ⟨?_, fun h => absurd hr2 (fun h' => hnl (h'.symm.trans h)), fun _ => ⟨hx.2.1, ?_⟩,
      fun hlf => ?_, fun _ _ _ => by rw [mat_len hr9]; exact hcnt, fun hlf x hxm => ?_⟩
    · intro x hxm
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hxm
      obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
      rw [hybF, (mat_wDat_eq hd).2.2.1, mat_pageW_key]; exact htk' j hjc
    · rw [hr2]
      refine ⟨rp', i, w, by rw [hns', if_neg (Ne.symm hlnl), if_pos rfl], by rw [hp2]; exact hw,
        by rw [hr3, hcid], hk0.symm, ?_⟩
      show (fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) y =
        wEntryBnd ((fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) nl) rp'.ws i
      rw [hybF]; simp only [hnlb, hp2]
    · have hnleaf : pageFlags pg ≠ leafPageFlag := by
        intro h; rw [hr4, h] at hlf; simp at hlf
      cases htk with
      | leaf _ pg' _ _ hpg' hl' _ _ => rw [hpg] at hpg'; cases hpg'; exact absurd hl' hnleaf
      | branch _ pg' _ _ kindN hpg' hbr' h2 _ hch hsub =>
        rw [hpg] at hpg'; cases hpg'
        refine ⟨by rw [mat_len hr9]; exact h2, decide (kindN = leafPageFlag), fun j x hj => ?_⟩
        obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
        obtain ⟨cpg, hcpg, hcc, hcf, hck⟩ := hch j hjc
        have hpj : x.pgid = W64 (branchPgid pg j : Int) := by
          rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]
        have hnm0 := hfree j hjc hbr'
        rw [← hpj] at hnm0
        refine ⟨fun l' hl' => (by rw [hnm0] at hl'; cases hl'), fun _ => ⟨cpg, ?_, hcc,
          by rw [hcf], ?_, ?_⟩⟩
        · rw [hpj, toNat_W64_of_lt _ (mat_branchPgid_lt pg j)]; exact hcpg
        · rw [hck, (mat_wDat_eq hd).2.2.1, (mat_pageW_branch pg j hnleaf).2]
        · rw [hpj, toNat_W64_of_lt _ (mat_branchPgid_lt pg j), mat_wEntryBnd hr9, hybF,
            mat_entryBnd_page _ pg j hjc hnleaf]
          exact hsub j hjc
    · have hfl : pageFlags pg = leafPageFlag := by rw [hr4] at hlf; simpa using hlf
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hxm
      obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
      obtain ⟨e1, -, -, e4⟩ := mat_wDat_eq hd
      obtain ⟨f1, -, -, f4⟩ := mat_pageW_leaf pg j hfl
      intro hbk h0 _
      rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)] at hbk
      rw [e4, f4] at h0 ⊢
      cases htk with
      | leaf _ pg' _ _ hpg' _ _ hbkt =>
        rw [hpg] at hpg'; cases hpg'
        exact hbkt j hjc hbk h0
      | branch _ pg' _ _ _ hpg' hbr' _ _ _ _ =>
        rw [hpg] at hpg'; cases hpg'
        rw [hfl] at hbr'; exact absurd hbr'.symm mat_branch_ne_leaf
  · -- an old node
    obtain ⟨ry0, hry0, a1, a2, a3, a4, -, a6, a7, a8⟩ := hold' y ry hy hyl
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hk3 y ry0 hry0
    have hb : (fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) y = bnd y := by
      simp only [if_neg hyl]
    refine ⟨by rw [hb, a3]; exact c1, fun hp => by rw [hb]; exact c2 (by rw [← a1]; exact hp),
      fun hp => ?_, fun hlf => ?_, by rw [a2, a8, a1, a3]; exact c5, ?_⟩
    · rw [a1] at hp
      obtain ⟨hk', rp0, i0, w0, hrp0, hw0, hpg0, hkey0', hbnd0⟩ := c3 hp
      obtain ⟨rp0', h1, -, -, h2, -⟩ := hnsB _ _ hrp0
      have hpl : ry0.nv.parent' ≠ l := hold _ (hpar y ry0 hry0 hp)
      refine ⟨by rw [a6]; exact hk', rp0', i0, w0, by rw [a1]; exact h1, by rw [h2]; exact hw0,
        by rw [a4]; exact hpg0, by rw [a7]; exact hkey0', ?_⟩
      rw [hb, a1, h2]
      simp only [if_neg hpl]; exact hbnd0
    · rw [a2] at hlf
      obtain ⟨h2, kind', hkd'⟩ := c4 hlf
      refine ⟨by rw [a3]; exact h2, kind', fun j w' hj => ?_⟩
      rw [a3] at hj
      obtain ⟨ha, hbb⟩ := hkd' j w' hj
      refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
      · rw [hnm'] at hl'
        split at hl'
        · rename_i hkw
          cases hl'
          obtain ⟨pg0, hpg0, -, hk0, -⟩ := hbb (by rw [hkw]; exact hnone)
          rw [hkw, hpg] at hpg0; cases hpg0
          exact ⟨r, by rw [hns', if_pos rfl], by rw [hr4]; exact hk0⟩
        · obtain ⟨r'', h1, h2⟩ := ha l' hl'
          obtain ⟨r3, h3, -, h4, -⟩ := hnsB _ _ h1
          exact ⟨r3, h3, h4.trans h2⟩
      · rw [hnm'] at hn
        split at hn
        · cases hn
        · obtain ⟨pg0, a1', a2', a3', a4', a5'⟩ := hbb hn
          exact ⟨pg0, a1', a2', a3', a4', by rw [hb, a3]; exact a5'⟩
    · rw [a2, a3]
      intro hlf x hx hbk h0 hno
      exact c6 hlf x hx hbk h0 hno

end childkeys

/-! ## `wOK_nodeAdded` -/

section main
variable [GooseExts]

/-- **Materializing a page position keeps `wOK`** (`Model/WOps`' `wOK_nodeAdded`, with three
premises `nodeAdded` lacks; see the module doc): the new node's nested buckets' values are in the
view or persistent (`hsrc`), the parent's `capOwn` is kept (`hcap`), an inline bucket's page's
entries are within the bound (`hinl`). -/
theorem wOK_nodeAdded' (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hok : wOK X) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent)
    (hsrc : ∀ B' r', X'.t.bs !! bl = some B' → B'.ns !! l = some r' → ∀ w ∈ r'.ws,
      isBktFlag w.flags → w.vs = Src.view ∨ w.vs = Src.own DFrac.discard)
    (hcap : ∀ B B' rp rp', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' →
      B.ns !! parent = some rp → B'.ns !! parent = some rp' → rp'.capOwn = rp.capOwn)
    (hinl : ∀ B, X.t.bs !! bl = some B → B.ib.root' = W64 0 → B.bv.rootNode' = null →
      ∀ j < pageCount B.ipg, leafKsize B.ipg j + leafVsize B.ipg j ≤ bboltEntryMax) :
    wOK X' := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hstrict := mat_strict X.v hv
  obtain ⟨B, pa, pg, r, ns', bv', hB, hwp, hnm, hl0, hlo, hrb, hrpar, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := h
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  have hc := wOK_bktClean X hok bl B hB
  have hr : matNew bl parent pg r :=
    ⟨hrb, hrpar, hrid, hrleaf, hru, hrs, hrcs, hrco, by rw [hrws, mat_pageWsAs_wDat], hrlive,
      hrkey, hrks⟩
  have hr9 := hr.2.2.2.2.2.2.2.2.1
  have hfresh : B.ns !! l = none := objs_none X.t l hlo' bl B hB
  have hB' : X'.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
    rw [hX']; exact GMap.lookup_insert _ _ _
  have hns'l : ns' !! l = some r := by
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;>
      exact GMap.lookup_insert _ _ _
  have hsrc' := hsrc _ r hB' hns'l
  obtain ⟨B1, hB1, hp⟩ := hpos
  rw [hB] at hB1; cases hB1
  subst hX'
  rcases hcase with ⟨hpn, hbv, hns⟩ | ⟨hpn, hbv, rp, rp', hrp, hbr, hc1, hc2, hc3, hc4, hc5, hcap, hc6, hns⟩
  · -- the root case
    subst hpn hbv hns
    rcases hp with ⟨-, hrn0, rfl⟩ | ⟨i, rp, w, hrp, -⟩
    rotate_left
    · have := ncol_nm (hc.2.2.2.2.2.2.2.1 null rp hrp)
      exact absurd rfl (hc.2.2.2.2.1 _ _ this).1
    have hns0 := (hc.2.2.1 hrn0).1
    have hnm0 := (hc.2.2.1 hrn0).2
    -- the page's facts
    have hfacts : pageTreeWF X.v.pages X.t.mv.pgid'.toNat pg pg.length ∧ pageGood pg ∧
        (pageHdr pg).id' = B.ib.root' ∧
        (B.ib.root' ≠ W64 0 → X.v.pages !! B.ib.root'.toNat = some pg) ∧
        (B.ib.root' = W64 0 → pageFlags pg = leafPageFlag ∧
          ∀ j < pageCount pg, leafFlags pg j % 2 = 0) ∧ leafBnd pg := by
      by_cases hin : B.ib.root' = W64 0
      · obtain ⟨-, -, hg, -⟩ := hc.1 hin hrn0
        have hpgB : pg = B.ipg := by
          unfold wpageAt at hwp
          simp only [hin, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hwp
          exact hwp.2.symm
        subst hpgB
        obtain ⟨g1, g2, g3, -, g5⟩ := hg
        refine ⟨pageTreeWF.leaf _ _ g2 g3 (fun i hi hb => ?_), ⟨fun _ i hi => ⟨(g5 i hi).1,
          fun hb => ?_⟩, fun hb => ?_⟩, ?_, fun h => absurd hin h, fun _ => ⟨g2, fun j hj => (g5 j hj).2⟩,
          fun _ j hj _ => hinl B hB hin hrn0 j hj⟩
        · have := (g5 i hi).2; rw [hb] at this; unfold bucketLeafFlag at this; omega
        · have := (g5 i hi).2; rw [hb] at this; unfold bucketLeafFlag at this; omega
        · rw [g2] at hb; exact absurd hb leaf_ne_branch
        · rw [hin]; apply BitVec.eq_of_toNat_eq; exact g1
      · have hpgv : X.v.pages !! B.ib.root'.toNat = some pg := by
          unfold wpageAt at hwp; rw [if_neg hin] at hwp
          cases h : X.v.pages !! B.ib.root'.toNat with
          | none => rw [h] at hwp; cases hwp
          | some pg0 => rw [h] at hwp; simp only [Option.map_some, Option.some.injEq,
                          Prod.mk.injEq] at hwp
                        rw [hwp.2]
        have htw := (hc.2.1 hin).2 hrn0
        obtain ⟨hid, -, hpt⟩ := mat_ptwf htw hpgv
        exact ⟨hpt, hstrict.1 _ pg hpgv, BitVec.eq_of_toNat_eq hid, fun _ => hpgv,
          fun h => absurd h hin, viewWF_leafBnd X.v hv _ pg hpgv⟩
    obtain ⟨hpt, hgood, hcid, hfile, hinl', hlb⟩ := hfacts
    have htk : B.ib.root' ≠ W64 0 → treeKeys X.v.pages B.ib.root'.toNat none none := by
      obtain ⟨bnd, hk1, -, -⟩ := (hok.2.1 bl B hB).1
      exact hk1 hrn0
    have hrid' : r.nv.pgid' = B.ib.root' := hrid.trans hcid
    have hns' := matR_ns B B.ib.root' l r hns0
    refine wOK_matX X bl l B.ib.root' B (matRBkt B B.ib.root' l r) r hok hB hlo'
      (matR_clean X.v _ bl B hstrict hc hrn0 l hl0 pg r hr hpt hgood hcid hfile hinl' hrins hrkn
        hsrc' (by
          by_cases hin : B.ib.root' = W64 0
          · intro _ i hi hb _
            have := (hinl' hin).2 i hi; rw [hb] at this; unfold bucketLeafFlag at this; omega
          · exact viewWF_leafInl X.v hv _ pg (hfile hin))
        (by
          by_cases hin : B.ib.root' = W64 0
          · intro _ i hi hb
            have := (hinl' hin).2 i hi; rw [hb] at this; unfold bucketLeafFlag at this; omega
          · exact viewWF_matNest X.v hv _ pg (hfile hin)))
      (matR_keys X.v _ bl B hstrict hc hrn0 l hl0 pg r hr hpt hgood hcid hfile hinl' htk)
      (matR_entryIn X.v _ bl B hstrict hc hrn0 l hl0 pg r hr hpt hgood hcid hfile hinl')
      rfl rfl (fun h => absurd h hl0) rfl (by rw [hns', if_pos rfl]) ?_ ?_ ?_
      (newNodeBnd pg r hr9 hrleaf (pageKeys_pos _ _ pg hpt hgood) hlb
        (fun hfl j hj hbk => by
          by_cases hin : B.ib.root' = W64 0
          · have := (hinl' hin).2 j hj; rw [hbk] at this; unfold bucketLeafFlag at this; omega
          · exact (hok.1.2.1.2.2.2.1 bl B hB _ _ pg (Or.inl ⟨hrn0, hin, rfl⟩)
              (ownHas.root _ pg (hfile hin)) (hfile hin) hfl j hj).2.1.2)
        (fun hnl j hj => by
          by_cases hin : B.ib.root' = W64 0
          · exact absurd (hinl' hin).1 hnl
          · exact pageKeys_le_of_treeKeysN X.v.pages _ bboltEntryMax
              (fun p pg0 ho hp hf j hj => by
                have := (hok.1.2.1.2.2.2.1 bl B hB _ p pg0 (Or.inl ⟨hrn0, hin, rfl⟩) ho hp hf j
                  hj).2.1.2
                omega)
              _ none none (htk hin) (ownHas.root _ pg (hfile hin)) pg (hfile hin) j hj)
        -- item 3/batch 43.4: the root bucket's root page's keys at most `MaxKeySize` (a leaf's:
        -- `posShape`'s name clause; a branch's: exact branch keys, `Write/RootKeys`)
        (fun hP => by
          have hBr : X.t.bs !! X.rl = some B := by rw [← hP]; exact hB
          have hin : B.ib.root' ≠ W64 0 := fun h => hok.1.2.1.2.2.2.2 B hBr h
          exact pageKeys_le_of_treeKeys X.v.pages _
            (posShape_rootLeaf X hok.1.2.1.2.2.2.1 B hBr _ (Or.inl ⟨hrn0, hin, rfl⟩))
            _ none none (htk hin) (ownHas.root _ pg (hfile hin)) pg (hfile hin))) (by rw [hrid'])
      (newNode_shape pg r _ hr9 hrleaf (fun hlf j hj => by
        by_cases hin : B.ib.root' = W64 0
        · -- an inline bucket's page: no bucket entries; `bl` is not the root bucket (batch 37:
          -- `txClean`'s `rootNotInline`)
          have h1 := (hinl' hin).2 j hj
          have hnr : bl ≠ X.rl := fun h => hok.1.2.1.2.2.2.2 B (h ▸ hB) hin
          unfold bucketLeafFlag; constructor
          · intro h; omega
          · intro h; exact absurd h hnr
        · exact (hok.1.2.1.2.2.2.1 bl B hB _ _ pg (Or.inl ⟨hrn0, hin, rfl⟩)
            (ownHas.root _ pg (hfile hin)) (hfile hin) hlf j hj).1))
      (fun k h => nm_ins_none B.nm _ k l h)
      (fun hb => by
        have hin : B.ib.root' ≠ W64 0 := by
          intro h0; rw [hrleaf, (hinl' h0).1] at hb; simp at hb
        exact Or.inl ⟨hrn0, hin, by rw [hrid']⟩)
    · intro y ry' hy
      rw [hns'] at hy
      split at hy
      · rename_i h; exact Or.inl h
      · cases hy
    · intro y ry hy; rw [hns0] at hy; cases hy
    · refine newNodePg X.v B.ib.root' pg r hr9 hrleaf hrkey ?_ (fun h0 => by rw [hrid']; exact hfile h0)
        (fun hb h0 => by rw [(hinl' h0).1] at hb; exact leaf_ne_branch hb)
      rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · -- the child case
    rcases hp with ⟨h0, -⟩ | ⟨i, rp0, w, hrp0, hbr0, hw, hwpg, hnone⟩
    · exact absurd h0 hpn
    subst hwpg hbv hns
    rw [hrp] at hrp0; cases hrp0
    have hroot : B.ib.root' ≠ W64 0 := by
      intro h0; have := hc.2.2.2.2.2.2.1 h0 parent rp hrp; rw [hbr] at this; cases this
    have hpg : X.v.pages !! w.pgid.toNat = some pg := by
      unfold wpageAt at hwp; rw [if_neg hroot] at hwp
      cases h : X.v.pages !! w.pgid.toNat with
      | none => rw [h] at hwp; cases hwp
      | some pg0 => rw [h] at hwp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwp
                    rw [hwp.2]
    have hrp' : (matBkt B w.pgid parent l rp' r).ns !! parent = some rp' := by
      rw [mat_ns, if_neg (fun h => by rw [h, hfresh] at hrp; cases hrp), if_pos rfl]
    have hp' : matParent rp rp' l := ⟨hc1, hc2, hc3, hc4, hc5, hc6, hcap B _ rp rp' hB hB' hrp hrp'⟩
    obtain ⟨⟨bnd, hkb, hbf⟩, hl0', ha, -⟩ := rblReady_of_wOK X hok bl B hB
    obtain ⟨-, -, -, hrpk3, -, -⟩ := hkb.2.2 parent rp hrp
    obtain ⟨-, kind, hkd⟩ := hrpk3 hbr
    obtain ⟨pg', hpg', hcnt, -, -, htkw⟩ := (hkd i w hw).2 hnone
    rw [hpg] at hpg'; cases hpg'
    have hx : matExtra r := by
      refine ⟨hrins, fun hn => ?_, hsrc'⟩
      have := hrkn.1 hn
      rw [this] at hr9
      have := mat_len hr9; simp at this; omega
    obtain ⟨-, -, -, -, -, hcid, hwfc, hpt, -⟩ :=
      mat_basic X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg r rp' hr hp'
    have hnsB := mat_nsB X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg
      r rp' hr hp'
    have hold := mat_old X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg
      r rp' hr hp'
    have hposw : posRoot B w.pgid.toNat := by
      refine Or.inr ⟨parent, i, ?_, BitVec.isLt _⟩
      rw [w64_toNat_cast]
      exact ⟨rp, w, hrp, hbr, hw, rfl, hnone⟩
    refine wOK_matX X bl l w.pgid B (matBkt B w.pgid parent l rp' r) r hok hB hlo'
      (mat_clean X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg r rp' hr
        hp' hx hcnt (Write.viewWF_leafInl X.v hv _ pg hpg) (viewWF_matNest X.v hv _ pg hpg))
      (bktKeys_of_rbl X.v _ _ (rblKeys_addChild X.v _ bl B hstrict hc parent rp i w hrp hbr hw
        hnone l hfresh hl0 pg hpg r rp' hr hp' hx bnd none (rblKeysB_of X.v B bnd hkb hbf hl0'))
        (rblAcyc_addChild X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg
          r rp' hr hp' ha))
      (entryIn_addChild X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg r
        rp' hr hp')
      rfl rfl (fun h => h) rfl (by rw [mat_ns, if_pos rfl]) ?_ ?_ ?_
      (newNodeBnd pg r hr9 hrleaf (pageKeys_pos _ _ pg hpt (hstrict.1 _ pg hpg))
        (viewWF_leafBnd X.v hv _ pg hpg)
        (fun hfl j hj _ => (hok.1.2.1.2.2.2.1 bl B hB _ _ pg hposw (ownHas.root _ pg hpg) hpg hfl j
          hj).2.1.2)
        (fun _ j hj => pageKeys_le_of_treeKeysN X.v.pages _ bboltEntryMax
          (fun p pg0 ho hp hf j hj => by
            have := (hok.1.2.1.2.2.2.1 bl B hB _ p pg0 hposw ho hp hf j hj).2.1.2
            omega)
          _ _ _ htkw (ownHas.root _ pg hpg) pg hpg j hj)
        -- item 3/batch 43.4: the root bucket's page keys at most `MaxKeySize` (as above)
        (fun hP => by
          have hBr : X.t.bs !! X.rl = some B := by rw [← hP]; exact hB
          exact pageKeys_le_of_treeKeys X.v.pages _
            (posShape_rootLeaf X hok.1.2.1.2.2.2.1 B hBr _ hposw)
            _ _ _ htkw (ownHas.root _ pg hpg) pg hpg)) (by rw [hrid, hcid])
      (newNode_shape pg r _ hr9 hrleaf (fun hlf j hj =>
        (hok.1.2.1.2.2.2.1 bl B hB _ _ pg hposw (ownHas.root _ pg hpg) hpg hlf j hj).1))
      (fun k h => nm_ins_none B.nm _ k l h)
      (fun _ => by rw [hrid, hcid]; exact hposw)
    · intro y ry' hy
      by_cases hyl : y = l
      · exact Or.inl hyl
      · obtain ⟨ry0, hry0, -, a2, a3, a4, -, -, a7, -⟩ := hold y ry' hy hyl
        exact Or.inr ⟨ry0, hry0, a2, a3, a4, a7⟩
    · intro y ry hy
      obtain ⟨ry', h1, -, -, -, h5, -⟩ := hnsB y ry hy
      exact ⟨ry', h1, h5⟩
    · refine newNodePg X.v B.ib.root' pg r hr9 hrleaf hrkey ?_
        (fun _ => by rw [hrid, hcid]; exact hpg) (fun _ => hroot)
      rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h

end main

/-! ## `bktLocalOK` through a materialization (`Cursor.node`'s callers, `seek_w` then `node`) -/

section localok
variable [GooseExts]

/-- `bktLocalOK` of a bucket grown by a fresh node. -/
theorem bktLocalOK_matX (X : WX) (bl l : Loc) (pgid : w64) (B B' : BRec) (r : NRec)
    (hb : bktLocalOK X bl) (hB : X.t.bs !! bl = some B)
    (hc' : bktClean X.v X.t.mv.pgid'.toNat bl B') (hk' : bktKeys X.v B')
    (hnew : B'.ns !! l = some r)
    (hnsN : ∀ y ry', B'.ns !! y = some ry' → y = l ∨ ∃ ry, B.ns !! y = some ry ∧
      ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws)
    (hleaf : nodePgLeaf r) : bktLocalOK (matX X bl l pgid B') bl := by
  obtain ⟨hlive, B0, hB0, -, -, hpl, hnl, hvw⟩ := hb
  rw [hB] at hB0; cases hB0
  refine ⟨hlive, B', by rw [matX_bs, if_pos rfl], hc', hk', ?_, ?_, hvw⟩
  · intro c C hC y ry hy
    rw [GMap.lookup_singleton_Some] at hC
    obtain ⟨rfl, rfl⟩ := hC
    rcases hnsN y ry hy with rfl | ⟨ry0, hry0, a1, a2⟩
    · rw [hnew] at hy; cases hy; exact hleaf
    · intro hlf x hx
      rw [a1] at hlf; rw [a2] at hx
      exact hpl bl B (GMap.lookup_singleton _ _) y ry0 hry0 hlf x hx
  · intro y ry hy
    rcases hnsN y ry hy with rfl | ⟨ry0, hry0, -⟩
    · exact mem_ins_self _ _ _
    · exact mem_ins_of_mem () (hnl y ry0 hry0)

/-- **A materialization keeps a searchable bucket searchable** (`bktLocalOK`), over a
well-formed view (`viewWF`: its pages' uniqueness gives the new node's distinct children and
disjoint positions; `bktLocalOK` alone does not), with `nodeAdded`'s missing facts as premises
(`hsrc`, `hcap`: batch 20). -/
theorem bktLocalOK_nodeAdded (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hv : viewWF X.v) (hb : bktLocalOK X bl) (h : nodeAdded X X' bl l pgid parent)
    (hpos : matPos X bl pgid parent)
    (hsrc : ∀ B' r', X'.t.bs !! bl = some B' → B'.ns !! l = some r' → ∀ w ∈ r'.ws,
      isBktFlag w.flags → w.vs = Src.view ∨ w.vs = Src.own DFrac.discard)
    (hcap : ∀ B B' rp rp', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' →
      B.ns !! parent = some rp → B'.ns !! parent = some rp' → rp'.capOwn = rp.capOwn) :
    bktLocalOK X' bl := by
  have hstrict := mat_strict X.v hv
  obtain ⟨B, pa, pg, r, ns', bv', hB, hwp, hnm, hl0, hlo, hrb, hrpar, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := h
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  have hb' := hb
  obtain ⟨-, B0, hB0, hc, ⟨bnd, hkb⟩, -, -⟩ := hb'
  rw [hB] at hB0; cases hB0
  have hr : matNew bl parent pg r :=
    ⟨hrb, hrpar, hrid, hrleaf, hru, hrs, hrcs, hrco, by rw [hrws, mat_pageWsAs_wDat], hrlive,
      hrkey, hrks⟩
  have hr9 := hr.2.2.2.2.2.2.2.2.1
  have hfresh : B.ns !! l = none := objs_none X.t l hlo' bl B hB
  have hB' : X'.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
    rw [hX']; exact GMap.lookup_insert _ _ _
  have hns'l : ns' !! l = some r := by
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;>
      exact GMap.lookup_insert _ _ _
  have hsrc' := hsrc _ r hB' hns'l
  have hleafr : nodePgLeaf r := by
    intro hlf x hx
    have hfl : pageFlags pg = leafPageFlag := by rw [hrleaf] at hlf; simpa using hlf
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨-, hd⟩ := mat_at hr9 j x hj
    rw [(mat_wDat_eq hd).2.1, (mat_pageW_leaf pg j hfl).2.1]
  obtain ⟨B1, hB1, hp⟩ := hpos
  rw [hB] at hB1; cases hB1
  subst hX'
  rcases hcase with ⟨hpn, hbv, hns⟩ | ⟨hpn, hbv, rp, rp', hrp, hbr, hc1, hc2, hc3, hc4, hc5, hcap', hc6, hns⟩
  · subst hpn hbv hns
    rcases hp with ⟨-, hrn0, rfl⟩ | ⟨i, rp, w, hrp, -⟩
    rotate_left
    · have := ncol_nm (hc.2.2.2.2.2.2.2.1 null rp hrp)
      exact absurd rfl (hc.2.2.2.2.1 _ _ this).1
    have hns0 := (hc.2.2.1 hrn0).1
    have hfacts : pageTreeWF X.v.pages X.t.mv.pgid'.toNat pg pg.length ∧ pageGood pg ∧
        (pageHdr pg).id' = B.ib.root' ∧
        (B.ib.root' ≠ W64 0 → X.v.pages !! B.ib.root'.toNat = some pg) ∧
        (B.ib.root' = W64 0 → pageFlags pg = leafPageFlag ∧
          ∀ j < pageCount pg, leafFlags pg j % 2 = 0) := by
      by_cases hin : B.ib.root' = W64 0
      · obtain ⟨-, -, hg, -⟩ := hc.1 hin hrn0
        have hpgB : pg = B.ipg := by
          unfold wpageAt at hwp
          simp only [hin, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hwp
          exact hwp.2.symm
        subst hpgB
        obtain ⟨g1, g2, g3, -, g5⟩ := hg
        refine ⟨pageTreeWF.leaf _ _ g2 g3 (fun i hi hb => ?_), ⟨fun _ i hi => ⟨(g5 i hi).1,
          fun hb => ?_⟩, fun hb => ?_⟩, ?_, fun h => absurd hin h,
          fun _ => ⟨g2, fun j hj => (g5 j hj).2⟩⟩
        · have := (g5 i hi).2; rw [hb] at this; unfold bucketLeafFlag at this; omega
        · have := (g5 i hi).2; rw [hb] at this; unfold bucketLeafFlag at this; omega
        · rw [g2] at hb; exact absurd hb leaf_ne_branch
        · rw [hin]; apply BitVec.eq_of_toNat_eq; exact g1
      · have hpgv : X.v.pages !! B.ib.root'.toNat = some pg := by
          unfold wpageAt at hwp; rw [if_neg hin] at hwp
          cases h : X.v.pages !! B.ib.root'.toNat with
          | none => rw [h] at hwp; cases hwp
          | some pg0 => rw [h] at hwp; simp only [Option.map_some, Option.some.injEq,
                          Prod.mk.injEq] at hwp
                        rw [hwp.2]
        have htw := (hc.2.1 hin).2 hrn0
        obtain ⟨hid, -, hpt⟩ := mat_ptwf htw hpgv
        exact ⟨hpt, hstrict.1 _ pg hpgv, BitVec.eq_of_toNat_eq hid, fun _ => hpgv,
          fun h => absurd h hin⟩
    obtain ⟨hpt, hgood, hcid, hfile, hinl'⟩ := hfacts
    have hns' := matR_ns B B.ib.root' l r hns0
    refine bktLocalOK_matX X bl l B.ib.root' B (matRBkt B B.ib.root' l r) r hb hB
      (matR_clean X.v _ bl B hstrict hc hrn0 l hl0 pg r hr hpt hgood hcid hfile hinl' hrins hrkn
        hsrc' (by
          by_cases hin : B.ib.root' = W64 0
          · intro _ i hi hb _
            have := (hinl' hin).2 i hi; rw [hb] at this; unfold bucketLeafFlag at this; omega
          · exact viewWF_leafInl X.v hv _ pg (hfile hin))
        (by
          by_cases hin : B.ib.root' = W64 0
          · intro _ i hi hb
            have := (hinl' hin).2 i hi; rw [hb] at this; unfold bucketLeafFlag at this; omega
          · exact viewWF_matNest X.v hv _ pg (hfile hin)))
      (matR_keys X.v _ bl B hstrict hc hrn0 l hl0 pg r hr hpt hgood hcid hfile hinl' (hkb.1 hrn0))
      (by rw [hns', if_pos rfl]) ?_ hleafr
    intro y ry' hy
    rw [hns'] at hy
    split at hy
    · rename_i h; exact Or.inl h
    · cases hy
  · rcases hp with ⟨h0, -⟩ | ⟨i, rp0, w, hrp0, hbr0, hw, hwpg, hnone⟩
    · exact absurd h0 hpn
    subst hwpg hbv hns
    rw [hrp] at hrp0; cases hrp0
    have hroot : B.ib.root' ≠ W64 0 := by
      intro h0; have := hc.2.2.2.2.2.2.1 h0 parent rp hrp; rw [hbr] at this; cases this
    have hpg : X.v.pages !! w.pgid.toNat = some pg := by
      unfold wpageAt at hwp; rw [if_neg hroot] at hwp
      cases h : X.v.pages !! w.pgid.toNat with
      | none => rw [h] at hwp; cases hwp
      | some pg0 => rw [h] at hwp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwp
                    rw [hwp.2]
    have hrp' : (matBkt B w.pgid parent l rp' r).ns !! parent = some rp' := by
      rw [mat_ns, if_neg (fun h => by rw [h, hfresh] at hrp; cases hrp), if_pos rfl]
    have hp' : matParent rp rp' l := ⟨hc1, hc2, hc3, hc4, hc5, hc6, hcap B _ rp rp' hB hB' hrp hrp'⟩
    obtain ⟨-, -, -, hrpk3, -, -⟩ := hkb.2.2 parent rp hrp
    obtain ⟨-, kind, hkd⟩ := hrpk3 hbr
    obtain ⟨pg', hpg', hcnt, -, -, htkw⟩ := (hkd i w hw).2 hnone
    rw [hpg] at hpg'; cases hpg'
    have hx : matExtra r := by
      refine ⟨hrins, fun hn => ?_, hsrc'⟩
      have := hrkn.1 hn
      rw [this] at hr9
      have := mat_len hr9; simp at this; omega
    have hold := mat_old X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg
      r rp' hr hp'
    refine bktLocalOK_matX X bl l w.pgid B (matBkt B w.pgid parent l rp' r) r hb hB
      (mat_clean X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg r rp' hr
        hp' hx hcnt (Write.viewWF_leafInl X.v hv _ pg hpg) (viewWF_matNest X.v hv _ pg hpg))
      ⟨_, bktKeys_addChild X.v _ bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl0 pg hpg
        r rp' hr hp' hx bnd hkb⟩
      (by rw [mat_ns, if_pos rfl]) ?_ hleafr
    intro y ry' hy
    by_cases hyl : y = l
    · exact Or.inl hyl
    · obtain ⟨ry0, hry0, -, a2, a3, -⟩ := hold y ry' hy hyl
      exact Or.inr ⟨ry0, hry0, a2, a3⟩

end localok

end Write


end bbolt
end EtcdGrove
end Perennial
