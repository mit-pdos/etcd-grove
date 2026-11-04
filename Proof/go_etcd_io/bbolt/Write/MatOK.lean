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
public import Proof.go_etcd_io.bbolt.Rebalance.RblMat
public import Proof.go_etcd_io.bbolt.Rebalance.RblReady
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSObjs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section bound
variable [GooseExts]

/-- A leaf page's plain entries are within `bboltEntryMax`. -/
def leafBnd (pg : List w8) : Prop :=
  pageFlags pg = leafPageFlag → ∀ i < pageCount pg, leafFlags pg i % 2 = 0 →
    leafKsize pg i + leafVsize pg i ≤ bboltEntryMax

/-- A bucket value whose leaves hold plain entries within the bound. -/
def bvBnd (P : Pages) (v : List w8) : Prop :=
  ∀ bpg, bktLeafPg P v bpg → ∀ j < pageCount bpg,
    leafFlags bpg j % 2 = 0 ∧ leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax

/-- A nested bucket's tree: its leaves hold plain entries within the bound. -/
def nestBnd (P : Pages) (r : Nat) : Prop :=
  ∀ id pg, ownHas P r id → P !! id = some pg → pageFlags pg = leafPageFlag →
    ∀ j < pageCount pg, leafFlags pg j % 2 = 0 ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax

def topPg (P : Pages) (pg : List w8) : Prop :=
  (pageFlags pg = leafPageFlag → ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag ∧
    bvBnd P (leafValue pg i)) ∧
  (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, rootShape P (branchPgid pg i))

def nestPg (P : Pages) (pg : List w8) : Prop :=
  (pageFlags pg = leafPageFlag → ∀ j < pageCount pg,
    leafFlags pg j % 2 = 0 ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax) ∧
  (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, nestBnd P (branchPgid pg i))

theorem topPg_of (P : Pages) (r : Nat) (pg : List w8) (hs : rootShape P r)
    (hpg : P !! r = some pg) : topPg P pg := by
  refine ⟨fun hl i hi => ?_, fun hb i hi => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hs r pg (ownHas.root _ pg hpg) hpg hl i hi
    exact ⟨h1, fun bpg hb j hj => ⟨(h3 bpg hb j hj).1, (h3 bpg hb j hj).2.2⟩⟩
  · intro id pg' ho hp hl'
    exact hs id pg' (ownHas.child _ pg i id hpg hb hi ho) hp hl'

theorem nestPg_of (P : Pages) (r : Nat) (pg : List w8) (hs : nestBnd P r)
    (hpg : P !! r = some pg) : nestPg P pg := by
  refine ⟨fun hl j hj => hs r pg (ownHas.root _ pg hpg) hpg hl j hj, fun hb i hi => ?_⟩
  intro id pg' ho hp hl'
  exact hs id pg' (ownHas.child _ pg i id hpg hb hi ho) hp hl'

theorem leaf_ne_branch : leafPageFlag ≠ branchPageFlag := by
  unfold branchPageFlag leafPageFlag; decide

/-- Every page a top-level or nested tree reaches has its plain entries within the bound. -/
theorem treeHas_leafBnd (P : Pages) (hwm : Nat) {root id : Nat} (h : treeHas P root id) :
    treeWF P hwm root → (rootShape P root ∨ nestBnd P root) →
      ∀ pg, P !! id = some pg → leafBnd pg :=
  treeHas.rec (pages := P)
    (motive_1 := fun root id _ => treeWF P hwm root → (rootShape P root ∨ nestBnd P root) →
      ∀ pg, P !! id = some pg → leafBnd pg)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len → (topPg P pg ∨ nestPg P pg) →
      ∀ pg', P !! id = some pg' → leafBnd pg')
    (motive_3 := fun v id _ => bucketWF P hwm v → bvBnd P v →
      ∀ pg', P !! id = some pg' → leafBnd pg')
    (fun root pg hpg _ hs pg' hpg' => by
      rw [hpg] at hpg'; cases hpg'
      intro hl i hi h0
      rcases hs with hs | hs
      · have := (hs root pg (ownHas.root _ pg hpg) hpg hl i hi).1
        unfold bucketLeafFlag at this; omega
      · exact (hs root pg (ownHas.root _ pg hpg) hpg hl i hi).2)
    (fun root pg id hpg _ ih hw hs => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        rw [hpg] at hpg'; cases hpg'
        refine ih _ hpt ?_
        rcases hs with hs | hs
        · exact Or.inl (topPg_of P root pg hs hpg)
        · exact Or.inr (nestPg_of P root pg hs hpg))
    (fun pg i id hfl hi _ ih len hpt hs => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl'.symm leaf_ne_branch
      | branch _ _ _ _ hch =>
        refine ih (hch i hi) ?_
        rcases hs with hs | hs
        · exact Or.inl (hs.2 hfl i hi)
        · exact Or.inr (hs.2 hfl i hi))
    (fun pg i id hfl hi hbf _ ih len hpt hs => by
      cases hpt with
      | leaf _ _ _ _ hb =>
        refine ih (hb i hi hbf) ?_
        rcases hs with hs | hs
        · exact (hs.1 hfl i hi).2
        · have := (hs.1 hfl i hi).1; rw [hbf] at this; unfold bucketLeafFlag at this; omega
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl' leaf_ne_branch)
    (fun v id hr _ ih hb hbv => by
      cases hb with
      | file _ _ _ ht =>
        refine ih ht (Or.inr ?_)
        intro id' pg ho hp hl j hj
        exact hbv pg (Or.inr ⟨hr, id', ho, hp, hl⟩) j hj
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb hbv => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ hfl hpt =>
        refine ih _ hpt (Or.inr ⟨fun _ j hj => hbv _ (Or.inl ⟨hr, rfl⟩) j hj, fun hb => ?_⟩)
        rw [hfl] at hb; exact absurd hb leaf_ne_branch)
    h

/-- **Every leaf page of a well-formed view has its plain entries within `bboltEntryMax`**
(`treeOK`'s `rootShape`: the root's leaves hold buckets only, their leaves plain entries within
the bound; every page of the view is the tree's). -/
theorem viewWF_leafBnd (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) : leafBnd pg := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  exact treeHas_leafBnd C.pages C.hwm hhas hok.1.1 (Or.inl hok.2.2.2.2.1) pg hpg

end bound

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

/-- **`wOK` of a bucket grown by a fresh node** (what both cases of `wOK_nodeAdded'` give). -/
theorem wOK_matX (X : WX) (bl l : Loc) (pgid : w64) (B B' : BRec) (r : NRec)
    (hok : wOK X) (hB : X.t.bs !! bl = some B) (hlo : X.t.objs !! l = none)
    (hc' : bktClean X.v X.t.mv.pgid'.toNat bl B') (hk' : bktKeys X.v B')
    (hent : ∀ k v, entryIn X.v B k v → entryIn X.v B' k v)
    (hib : B'.ib = B.ib) (hbm : B'.bm = B.bm)
    (hrn : B'.bv.rootNode' = null → B.bv.rootNode' = null)
    (hnew : B'.ns !! l = some r)
    (hnsN : ∀ y ry', B'.ns !! y = some ry' → y = l ∨ ∃ ry, B.ns !! y = some ry ∧
      ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws ∧ ry'.nv.pgid' = ry.nv.pgid' ∧
      ry'.key = ry.key)
    (hnsO : ∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧
      ry'.nv.pgid' = ry.nv.pgid')
    (hpg : nodePg X.v B.ib.root' r)
    (hbnd : ∀ w ∈ r.ws, 0 < w.key.length ∧ (r.nv.isLeaf' = true → ¬ isBktFlag w.flags →
      w.key.length + w.value.length ≤ bboltEntryMax))
    (hpid : r.nv.pgid'.toNat = pgid.toNat) :
    wOK (matX X bl l pgid B') := by
  obtain ⟨⟨hw, hpm, hpg2, htxid, hrl, hbs⟩, hkn, htp, heb, hho, ⟨hl1, hl2, hl3, hl4, hl5⟩, hnl,
    hv⟩ := hok
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
  have hlB : B.ns !! l = none := (Write.objs_none X.t l hlo).2 bl B hB
  -- the objects grow
  have hobj : ∀ k, (X.t.objs !! k).isSome = true →
      ((matX X bl l pgid B').t.objs !! k).isSome = true := by
    refine objs_isSome_mono X.t (matX X bl l pgid B').t (fun k h => h)
      (fun c h => by rw [hdom]; exact h) ?_
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
    exact Or.inr ⟨bl, B', by rw [hbs', if_pos rfl], Or.inr (by rw [hnew]; rfl)⟩
  have hldead : X.t.dead !! l = none := by
    cases h : X.t.dead !! l with
    | none => rfl
    | some o =>
      have : (X.t.objs !! l).isSome = true := by
        rw [objs_isSome]; exact Or.inl (by rw [h]; rfl)
      rw [hlo] at this; cases this
  refine ⟨⟨hw, hpm, hpg2, htxid, by rw [hdom]; exact hrl, fun c C hC => ?_⟩, fun c C hC => ?_,
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
      obtain ⟨C2, v, hC2, hin, h16, hinl, hroot, hrn2⟩ := (hkn c C0 hC0).2 k c' hk
      by_cases hcb : c' = bl
      · subst hcb
        rw [hB] at hC2; cases hC2
        exact ⟨B', v, by rw [hbs', if_pos rfl], he k v hin, h16, hinl, by rw [hib]; exact hroot,
          fun h0 => by rw [hib]; exact hrn2 (hrn h0)⟩
      · exact ⟨C2, v, by rw [hbs', if_neg hcb]; exact hC2, he k v hin, h16, hinl, hroot, hrn2⟩
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
      · rw [a1, a2]; exact heb c B hB y ry0 hry0
    · exact heb c C hC0 y ry hy
  · -- handles
    intro b nm hb; exact hobj b (hho b nm hb)
  · -- live: the root
    exact mem_ins_of_mem () hl1
  · intro k hk
    by_cases hkl : k = l
    · subst hkl; exact hlobj
    · exact hobj k (hl2 k (mem_of_mem_ins_ne hk hkl))
  · intro c C hC
    rcases hcase c C hC with ⟨rfl, rfl⟩ | ⟨-, hC0⟩
    · exact mem_ins_of_mem () (hl3 c B hB)
    · exact mem_ins_of_mem () (hl3 c C hC0)
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

end Write

end bbolt
end EtcdGrove
end Perennial
