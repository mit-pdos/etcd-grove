/-
The writer's records right after `beginRWTx` (U5 of `notes/bbolt-proof-plan.md`; design §3.13):
`wx0`, the root bucket at `txRoot tx` without root node or caches, on the committed state's view.
Its pure facts: `wOK`, its data the committed data (`wtxData_wx0`), `gensOK`, and the freelist
facts `flViewU` asks of it.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Fuel
public import Proof.go_etcd_io.bbolt.Read.BktOK
public import Proof.go_etcd_io.bbolt.Inv.MatReady
public import Proof.go_etcd_io.bbolt.Txn.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section winit
variable [GooseExts]

/-- The root bucket's record right after `Tx.init`: no root node, empty caches. -/
def brec0 (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) : BRec :=
  ⟨bv, ib, ∅, ∅, ∅, [], Src.own DFrac.discard, PageSt.none⟩

/-- **The writer's records right after `Tx.init`** (and `db.rwtx = t`): the root bucket at `rl`
without root node or caches, nothing else. -/
def wx0 (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) : WX :=
  { t := { t := t, mv := mv, pm := ∅, bufs := ∅, bs := GMap.singleton rl (brec0 bv ib),
           dead := ∅, deadB := ∅ },
    live := ∅, liveB := GMap.singleton rl (), handles := ∅, nloc := ∅, v := v, rl := rl }

/-- What `Tx.init` leaves for a writer (pure): writable, the meta copy one txid on and the
committed state's high-water mark, the root bucket's header at the committed root, no root node,
no page. -/
structure Init0 (C : CommitSt) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket)
    (ib : InBucket) : Prop where
  writable : t.writable' = true
  txid : mv.txid'.toNat = C.txid + 1
  pgid : mv.pgid'.toNat = C.hwm
  root : ib.root' = W64 (C.root : Int)
  rootNode : bv.rootNode' = null
  page : bv.page' = null

theorem treeOK_root (C : CommitSt) (htree : treeOK C) : 2 ≤ C.root ∧ C.root < C.hwm := by
  obtain ⟨⟨hwf, -⟩, -⟩ := htree
  cases hwf with
  | page _ _ h2 hlt _ _ _ _ => exact ⟨h2, hlt⟩

theorem wx0_bs (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) (bl : Loc) :
    (wx0 rl t mv bv ib v).t.bs !! bl = if rl = bl then some (brec0 bv ib) else none := by
  simp [wx0]

theorem wx0_bs_some (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) (bl : Loc) (B : BRec) (h : (wx0 rl t mv bv ib v).t.bs !! bl = some B) :
    bl = rl ∧ B = brec0 bv ib := by
  rw [wx0_bs] at h
  split at h
  · cases h; rename_i h; exact ⟨h.symm, rfl⟩
  · cases h

/-- **The initial records are well-formed.** -/
theorem wOK_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket)
    (ib : InBucket) (htree : treeOK C) (hi : Init0 C t mv bv ib) :
    wOK (wx0 rl t mv bv ib (View.ofC b C)) := by
  obtain ⟨h2, hlt⟩ := treeOK_root C htree
  have hhwm : C.hwm < 2 ^ 64 := by have := hi.pgid; rw [← this]; exact BitVec.isLt _
  have hr64 : C.root < 2 ^ 64 := by omega
  have hrt : ib.root'.toNat = C.root := by rw [hi.root]; exact toNat_W64_of_lt _ hr64
  have hr0 : ib.root' ≠ W64 0 := by
    intro e; rw [e] at hrt; simp at hrt; omega
  have hbs := wx0_bs_some rl t mv bv ib (View.ofC b C)
  have hrt' : (brec0 bv ib).ib.root'.toNat = C.root := hrt
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hi.writable
  · rfl
  · show 2 ≤ mv.pgid'.toNat; rw [hi.pgid]; omega
  · show C.txid + 1 = mv.txid'.toNat; rw [hi.txid]
  · simp [wx0]
  · intro bl B hB
    obtain ⟨rfl, rfl⟩ := hbs bl B hB
    refine ⟨?_, fun name c h => by simp [brec0] at h⟩
    show bktClean (View.ofC b C) mv.pgid'.toNat bl (brec0 bv ib)
    rw [hi.pgid]
    refine ⟨fun h => absurd h hr0, fun _ => ⟨by rw [hrt']; exact hlt, fun _ => by
      rw [hrt']; exact htree.1.1⟩, fun _ => ⟨rfl, rfl⟩, fun h => absurd hi.rootNode h,
      fun c l h => by simp [brec0] at h, fun _ => hi.page, fun h => absurd h hr0,
      fun l r h => by simp [brec0] at h, ?_, ?_⟩
    · intro l1 i1 c1 l2 i2 c2 h1
      obtain ⟨r, -, h, -⟩ := h1; simp [brec0] at h
    · intro l i c h1
      obtain ⟨r, -, h, -⟩ := h1; simp [brec0] at h
  · intro bl B hB
    obtain ⟨rfl, rfl⟩ := hbs bl B hB
    refine ⟨⟨fun _ => (none, none), fun _ _ => by rw [hrt']; exact htree.1.2.2.1,
      fun r h => by simp [brec0] at h, fun l r h => by simp [brec0] at h⟩, ?_⟩
    intro k c h; simp [brec0] at h
  · intro bl B hB l r h
    obtain ⟨rfl, rfl⟩ := hbs bl B hB; simp [brec0] at h
  · intro bl B hB l r h
    obtain ⟨rfl, rfl⟩ := hbs bl B hB; simp [brec0] at h
  · intro b' nm h; simp [wx0] at h
  · refine ⟨by simp [wx0, Membership.mem], fun l h => by simp [wx0, Membership.mem] at h, ?_,
      fun bl B l r hB h => by obtain ⟨rfl, rfl⟩ := hbs bl B hB; simp [brec0] at h,
      fun l h => by simp [wx0] at h⟩
    intro bl B hB
    obtain ⟨rfl, rfl⟩ := hbs bl B hB
    simp [wx0, Membership.mem]
  · intro n b' p h; simp [wx0] at h
  · exact ⟨C, htree, rfl⟩

/-- **The initial records' generations**: no handle, no opened bucket. -/
theorem gensOK_wx0 (T : TxView) (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket)
    (ib : InBucket) (v : View) : gensOK T (wx0 rl t mv bv ib v) := by
  refine ⟨fun b n g h => by simp [wx0] at h, fun n b' h => ?_⟩
  simp [bktLoc, wx0, brec0] at h

/-- The initial records' logical tree: the root bucket's is the view's pages. -/
theorem ltree_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket)
    (ib : InBucket) (hr0 : ib.root' ≠ W64 0) (bl : Loc) (pid : w64) :
    ltree (wx0 rl t mv bv ib (View.ofC b C)) bl pid =
      if rl = bl then (C.pages !! pid.toNat).map
        (fun pg => (decide (pageFlags pg = leafPageFlag), pageWs pg)) else none := by
  unfold ltree
  rw [wx0_bs]
  have hr0' : ¬ ib.root' = 0#64 := by simpa using hr0
  by_cases h : rl = bl
  · have hres : resolve (brec0 bv ib) pid = none := by
      simp [resolve, brec0, hr0']
    have hwp : wpageAt (View.ofC b C) (brec0 bv ib) pid =
        (C.pages !! pid.toNat).map fun pg => (b +ₗ ((pid.toNat * 4096 : Nat) : Int), pg) := by
      simp [wpageAt, brec0, hr0', View.ofC]
    simp only [h, ↓reduceIte, hres]
    simp only [wx0]
    rw [hwp, Option.map_map]
    rfl
  · simp only [h, ↓reduceIte]

theorem branchPgid_toNat (pg : List w8) (i : Nat) :
    (W64 (branchPgid pg i : Int)).toNat = branchPgid pg i := by
  unfold branchPgid; simp

/-- The initial root bucket's leaves are the view tree's, read as entries. -/
theorem lleaves_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (hr0 : ib.root' ≠ W64 0) :
    ∀ n pid, lleaves (ltree (wx0 rl t mv bv ib (View.ofC b C))) rl n pid =
      (leavesF n C.pages pid.toNat).map pageWs
  | 0, _ => rfl
  | n + 1, pid => by
    simp only [lleaves, leavesF]
    rw [ltree_wx0 C b rl t mv bv ib hr0, if_pos rfl]
    cases hp : C.pages !! pid.toNat with
    | none => rfl
    | some pg =>
      simp only [Option.map_some]
      by_cases hl : pageFlags pg = leafPageFlag
      · simp [hl]
      · simp only [hl, decide_false, ite_false]
        rw [List.map_flatMap]
        unfold pageWs
        rw [List.flatMap_map]
        apply Write.flatMap_congr'
        intro i _
        have : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by simp [pageW, hl]
        rw [this, lleaves_wx0 C b rl t mv bv ib hr0 n, branchPgid_toNat]; rfl

theorem filterMap_eq_map_of {α β : Type} (l : List α) (f : α → Option β) (g : α → β)
    (h : ∀ a ∈ l, f a = some (g a)) : l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, List.map_cons, h a List.mem_cons_self]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem isBktFlag_of_mod (f : Nat) (h : f % 2 = 1) : isBktFlag (W32 (f : Int)) := by
  unfold isBktFlag
  intro e
  have := congrArg BitVec.toNat e
  simp [BitVec.toNat_and] at this
  omega

/-- The initial root bucket's entries are the view tree's (all buckets: `rootShape`). -/
theorem rootEnts_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (htree : treeOK C) (hi : Init0 C t mv bv ib) :
    rootEnts (wx0 rl t mv bv ib (View.ofC b C)) = treeEntries C.pages C.root := by
  obtain ⟨h2, hlt⟩ := treeOK_root C htree
  have hhwm : C.hwm < 2 ^ 64 := by have := hi.pgid; rw [← this]; exact BitVec.isLt _
  have hrt : ib.root'.toNat = C.root := by rw [hi.root]; exact toNat_W64_of_lt _ (by omega)
  have hr0 : ib.root' ≠ W64 0 := by
    intro e; rw [e] at hrt; simp at hrt; omega
  have hv : viewWF (wx0 rl t mv bv ib (View.ofC b C)).v := ⟨C, htree, rfl⟩
  -- the leaves
  have hroot : (wx0 rl t mv bv ib (View.ofC b C)).rootPid (wx0 rl t mv bv ib (View.ofC b C)).rl = ib.root' := by
    simp [WX.rootPid, wx0_bs, brec0, wx0]
  have hleaves : (wx0 rl t mv bv ib (View.ofC b C)).leaves (wx0 rl t mv bv ib (View.ofC b C)).rl = (treeLeaves C.pages C.root).map pageWs := by
    unfold WX.leaves
    have hfuel : (wx0 rl t mv bv ib (View.ofC b C)).fuel = (C.pages.size + 1) + (wx0 rl t mv bv ib (View.ofC b C)).t.bs.size := by
      simp only [WX.fuel]; show (View.ofC b C).pages.size + _ + 1 = _; simp [View.ofC]; omega
    rw [hfuel, hroot]
    rw [Write.lleaves_fuel_stable (ltree (wx0 rl t mv bv ib (View.ofC b C))) (wx0 rl t mv bv ib (View.ofC b C)).rl (Write.treeMeasure (wx0 rl t mv bv ib (View.ofC b C)).v.pages) ?_ _ _ _ ?_]
    · show lleaves (ltree (wx0 rl t mv bv ib (View.ofC b C))) rl _ _ = _
      rw [lleaves_wx0 C b rl t mv bv ib hr0, hrt]; rfl
    · intro pid ws hL w hw
      rw [show (wx0 rl t mv bv ib (View.ofC b C)).rl = rl from rfl, ltree_wx0 C b rl t mv bv ib hr0, if_pos rfl] at hL
      cases hp : C.pages !! pid.toNat with
      | none => rw [hp] at hL; cases hL
      | some pg =>
        rw [hp] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
        obtain ⟨hnl, rfl⟩ := hL
        have hpg : (wx0 rl t mv bv ib (View.ofC b C)).v.pages !! pid.toNat = some pg := hp
        have hb : pageFlags pg = branchPageFlag := by
          rcases (viewWF_page_ready (wx0 rl t mv bv ib (View.ofC b C)).v hv pid.toNat pg hpg).2.2.1 with h | h
          · exact absurd h hnl
          · exact h
        unfold pageWs at hw
        rw [List.mem_map] at hw
        obtain ⟨i, hi', rfl⟩ := hw
        have : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by simp [pageW, hnl]
        rw [this]
        exact Write.treeMeasure_child (wx0 rl t mv bv ib (View.ofC b C)).v hv pid pg hpg hb i (List.mem_range.1 hi')
    · have := Write.treeMeasure_le C.pages ib.root'
      show Write.treeMeasure C.pages ib.root' < C.pages.size + 1
      omega
  -- the root bucket's entries are all buckets
  have hents : rootEnts (wx0 rl t mv bv ib (View.ofC b C)) = treeEntries C.pages C.root := by
    unfold rootEnts treeEntries
    rw [hleaves, List.flatMap_map]
    apply Write.flatMap_congr'
    intro pg hpg
    obtain ⟨id, -, -, hown, hpid, hleaf, -⟩ :=
      leavesF_page C.pages C.hwm _ C.root none none htree.1.1 htree.1.2.2.1 pg hpg
    have hrs := htree.2.2.2.2.1 id pg hown hpid hleaf
    unfold pageWs leafEnts
    rw [List.filterMap_map]
    apply filterMap_eq_map_of
    intro i hi'
    have hi'' := List.mem_range.1 hi'
    have hf := (hrs i hi'').1
    simp only [Function.comp, pageW, hleaf, ite_true]
    rw [if_pos (by
      have := isBktFlag_of_mod (leafFlags pg i) (by rw [hf]; rfl)
      exact decide_eq_true this)]
  exact hents

/-- **The initial records hold the committed data.** -/
theorem wtxData_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (htree : treeOK C) (hi : Init0 C t mv bv ib) :
    wtxData (wx0 rl t mv bv ib (View.ofC b C)) = treeData C := by
  have hents := rootEnts_wx0 C b rl t mv bv ib htree hi
  unfold wtxData treeData
  rw [hents]
  congr 1
  apply List.map_congr_left
  intro e _
  have : bktDataOf (wx0 rl t mv bv ib (View.ofC b C)) e.1 e.2 = bktOfPage C.pages e.2 := by
    simp [bktDataOf, wx0_bs, brec0, wx0, View.ofC]
  rw [this]

/-! ## `covU` of the initial records -/

private theorem treeHas_trans0 {P : Pages} {a b c : Nat} (h1 : treeHas P a b) (h2 : treeHas P b c) :
    treeHas P a c := by
  have key : ∀ {a b}, treeHas P a b → ∀ c, treeHas P b c → treeHas P a c := fun {a b} h =>
    treeHas.rec (pages := P)
      (motive_1 := fun a b _ => ∀ c, treeHas P b c → treeHas P a c)
      (motive_2 := fun pg b _ => ∀ c, treeHas P b c → pageHas P pg c)
      (motive_3 := fun v b _ => ∀ c, treeHas P b c → bucketHas P v c)
      (fun _ _ _ c h => h)
      (fun a pg b hpg _ ih c h => treeHas.sub a pg c hpg (ih c h))
      (fun pg i b hfl hi _ ih c h => pageHas.child pg i c hfl hi (ih c h))
      (fun pg i b hfl hi hbf _ ih c h => pageHas.bucket pg i c hfl hi hbf (ih c h))
      (fun v b hr _ ih c h => bucketHas.file v c hr (ih c h))
      (fun v b hr _ ih c h => bucketHas.inline v c hr (ih c h))
      h
  exact key h1 c h2

private theorem bucketHas_page0 {P : Pages} {v : List w8} {y : Nat} (h : bucketHas P v y) :
    ∃ pg, P !! y = some pg :=
  bucketHas.rec (pages := P)
    (motive_1 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_2 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_3 := fun _ y _ => ∃ pg, P !! y = some pg)
    (fun _ pg hpg => ⟨pg, hpg⟩) (fun _ _ _ _ _ ih => ih) (fun _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) h

private theorem ownHas_treeHas0 {P : Pages} {c p : Nat} (h : ownHas P c p) : treeHas P c p := by
  induction h with
  | root r pg hpg => exact treeHas.root r pg hpg
  | child r pg i id hpg hb hi _ ih => exact treeHas.sub r pg id hpg (pageHas.child pg i id hb hi ih)

private theorem own_bucket_treeHas {P : Pages} {c L : Nat} (h : ownHas P c L) {pg : List w8}
    (hpg : P !! L = some pg) (hl : pageFlags pg = leafPageFlag) {i : Nat} (hi : i < pageCount pg)
    (hbf : leafFlags pg i % 2 = bucketLeafFlag) {d : Nat} (hd : bucketHas P (leafValue pg i) d) :
    treeHas P c d :=
  treeHas_trans0 (ownHas_treeHas0 h) (treeHas.sub L pg d hpg (pageHas.bucket pg i d hl hi hbf hd))

private theorem leaf_ne_branch {pg : List w8} (hl : pageFlags pg = leafPageFlag)
    (hb : pageFlags pg = branchPageFlag) : False := by
  rw [hl] at hb; simp [leafPageFlag, branchPageFlag] at hb

/-- No page of a bucket tree's own pages is in one of its leaves' nested buckets. -/
theorem own_not_bucket (P : Pages) (hu : viewUnique P) {r a : Nat} (ha : ownHas P r a) :
    ∀ {L : Nat} {pgL : List w8} {i : Nat}, ownHas P r L → P !! L = some pgL →
      pageFlags pgL = leafPageFlag → i < pageCount pgL → leafFlags pgL i % 2 = bucketLeafFlag →
      bucketHas P (leafValue pgL i) a → False := by
  induction ha with
  | root r pg hpg =>
    intro L pgL i hL hpgL hl hi hbf hd
    cases hL with
    | root _ pg' hpg' =>
      exact (hu.2 r _ hpgL hl).2 i hi hbf hd
    | child _ pg' j _ hpg' hb hj hL' =>
      have e := hpg.symm.trans hpg'; cases e
      exact (hu.1 r pg hpg hb).2 j hj (own_bucket_treeHas hL' hpgL hl hi hbf hd)
  | child r pg j a hpg hb hj ha ih =>
    intro L pgL i hL hpgL hl hi hbf hd
    cases hL with
    | root _ pg' hpg' =>
      have e := hpg.symm.trans hpgL; cases e
      exact leaf_ne_branch hl hb
    | child _ pg' k _ hpg' hb' hk hL' =>
      have e := hpg.symm.trans hpg'; cases e
      by_cases hkj : k = j
      · subst hkj; exact ih hL' hpgL hl hi hbf hd
      · exact (hu.1 r pg hpg hb).1 k j hk hj hkj a (own_bucket_treeHas hL' hpgL hl hi hbf hd)
          (ownHas_treeHas0 ha)

/-- Two leaf entries of a bucket tree whose nested buckets share a page are one entry. -/
theorem bucket_unique (P : Pages) (hu : viewUnique P) {r L1 : Nat} (h1 : ownHas P r L1) :
    ∀ {L2 : Nat} {pg1 pg2 : List w8} {i1 i2 d : Nat}, ownHas P r L2 →
      P !! L1 = some pg1 → pageFlags pg1 = leafPageFlag → i1 < pageCount pg1 →
      leafFlags pg1 i1 % 2 = bucketLeafFlag →
      P !! L2 = some pg2 → pageFlags pg2 = leafPageFlag → i2 < pageCount pg2 →
      leafFlags pg2 i2 % 2 = bucketLeafFlag →
      bucketHas P (leafValue pg1 i1) d → bucketHas P (leafValue pg2 i2) d → L1 = L2 ∧ i1 = i2 := by
  induction h1 with
  | root r pg hpg =>
    intro L2 pg1 pg2 i1 i2 d hL2 hp1 hl1 hi1 hb1 hp2 hl2 hi2 hb2 hd1 hd2
    cases hL2 with
    | root _ pg' hpg' =>
      have e := hp1.symm.trans hp2; cases e
      refine ⟨rfl, ?_⟩
      by_cases hne : i1 = i2
      · exact hne
      · exact ((hu.2 r pg1 hp1 hl1).1 i1 i2 hi1 hi2 hne hb1 hb2 d hd1 hd2).elim
    | child _ pg' k _ hpg' hb' _ _ =>
      have e := hp1.symm.trans hpg'; cases e
      exact (leaf_ne_branch hl1 hb').elim
  | child r pg j L1 hpg hb hj h1 ih =>
    intro L2 pg1 pg2 i1 i2 d hL2 hp1 hl1 hi1 hb1 hp2 hl2 hi2 hb2 hd1 hd2
    cases hL2 with
    | root _ pg' hpg' =>
      have e := hpg.symm.trans hp2; cases e
      exact (leaf_ne_branch hl2 hb).elim
    | child _ pg' k _ hpg' hb' hk hL2' =>
      have e := hpg.symm.trans hpg'; cases e
      by_cases hkj : k = j
      · subst hkj; exact ih hL2' hp1 hl1 hi1 hb1 hp2 hl2 hi2 hb2 hd1 hd2
      · exact ((hu.1 r pg hpg hb).1 k j hk hj hkj d (own_bucket_treeHas hL2' hp2 hl2 hi2 hb2 hd2)
          (own_bucket_treeHas h1 hp1 hl1 hi1 hb1 hd1)).elim

/-- A position of the initial root bucket with a page is a page of the view tree's own pages. -/
theorem lposF_wx0_own (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (hr0 : ib.root' ≠ W64 0) (htree : treeOK C) :
    ∀ n p pid pg, pid ∈ lposF (ltree (wx0 rl t mv bv ib (View.ofC b C))) rl n p →
      C.pages !! pid.toNat = some pg → ownHas C.pages p.toNat pid.toNat
  | 0, _, _, _, h, _ => by simp [lposF] at h
  | n + 1, p, pid, pg, h, hpg => by
    simp only [lposF] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ownHas.root _ pg hpg
    · rw [ltree_wx0 C b rl t mv bv ib hr0, if_pos rfl] at h
      cases hp : C.pages !! p.toNat with
      | none => rw [hp] at h; simp at h
      | some pgp =>
        rw [hp] at h
        by_cases hl : pageFlags pgp = leafPageFlag
        · simp [hl] at h
        · simp only [Option.map_some, hl, decide_false] at h
          rw [List.mem_flatMap] at h
          obtain ⟨w, hw, hm⟩ := h
          unfold pageWs at hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, rfl⟩ := hw
          have hpgid : (pageW pgp i).pgid = W64 (branchPgid pgp i : Int) := by simp [pageW, hl]
          rw [hpgid] at hm
          have ih := lposF_wx0_own C b rl t mv bv ib hr0 htree n _ pid pg hm hpg
          rw [branchPgid_toNat] at ih
          have hv : viewWF (View.ofC b C) := ⟨C, htree, rfl⟩
          have hb : pageFlags pgp = branchPageFlag := by
            rcases (viewWF_page_ready (View.ofC b C) hv p.toNat pgp hp).2.2.1 with h | h
            · exact absurd h hl
            · exact h
          exact ownHas.child _ pgp i _ hp hb (List.mem_range.1 hi) ih

/-- An entry of the initial root bucket: a bucket entry of a leaf of the view tree's own pages. -/
theorem rootEnts_wx0_mem (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (htree : treeOK C) (hi : Init0 C t mv bv ib)
    (n : GoString) (v : List w8) (h : (n, v) ∈ rootEnts (wx0 rl t mv bv ib (View.ofC b C))) :
    ∃ L pg i, ownHas C.pages C.root L ∧ C.pages !! L = some pg ∧ pageFlags pg = leafPageFlag ∧
      i < pageCount pg ∧ leafFlags pg i % 2 = bucketLeafFlag ∧ n = leafKey pg i ∧
      v = leafValue pg i := by
  rw [rootEnts_wx0 C b rl t mv bv ib htree hi] at h
  unfold treeEntries at h
  rw [List.mem_flatMap] at h
  obtain ⟨pg, hpg, he⟩ := h
  obtain ⟨id, -, -, hown, hpid, hleaf, -⟩ :=
    leavesF_page C.pages C.hwm _ C.root none none htree.1.1 htree.1.2.2.1 pg hpg
  unfold leafEnts at he
  rw [List.mem_map] at he
  obtain ⟨i, hi', he⟩ := he
  cases he
  have hi'' := List.mem_range.1 hi'
  exact ⟨id, pg, i, hown, hpid, hleaf, hi'', (htree.2.2.2.2.1 id pg hown hpid hleaf i hi'').1,
    rfl, rfl⟩

/-- **Every covered slot of the initial records is covered once.** -/
theorem covU_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (htree : treeOK C) (hi : Init0 C t mv bv ib) :
    covU (wx0 rl t mv bv ib (View.ofC b C)) := by
  obtain ⟨h2, hlt⟩ := treeOK_root C htree
  have hhwm : C.hwm < 2 ^ 64 := by have := hi.pgid; rw [← this]; exact BitVec.isLt _
  have hrt : ib.root'.toNat = C.root := by rw [hi.root]; exact toNat_W64_of_lt _ (by omega)
  have hr0 : ib.root' ≠ W64 0 := by
    intro e; rw [e] at hrt; simp at hrt; omega
  have hr0' : ¬ ib.root' = 0#64 := by simpa using hr0
  have hu : viewUnique C.pages := htree.1.2.1.2
  have hdis : pagesDisjoint C.pages := htree.2.2.1
  -- a position's cover: its page, own in the view tree
  have hpos : ∀ bl pid s, coverW (wx0 rl t mv bv ib (View.ofC b C)) s (.pos bl pid) →
      bl = rl ∧ ∃ pg, C.pages !! pid.toNat = some pg ∧ ownHas C.pages C.root pid.toNat ∧
        pid.toNat ≤ s ∧ s < pid.toNat + (1 + pageOverflow pg) := by
    intro bl pid s hc
    obtain ⟨hbs, hmem, e, he, hs1, hs2⟩ := hc
    have hbl : bl = rl := by
      rw [wx0_bs] at hbs; split at hbs
      · rename_i h; exact h.symm
      · exact absurd rfl hbs
    subst hbl
    refine ⟨rfl, ?_⟩
    unfold WX.posExtent at he
    rw [wx0_bs, if_pos rfl] at he
    have hres : resolve (brec0 bv ib) pid = none := by simp [resolve, brec0, hr0']
    simp only [hres] at he
    by_cases hp0 : pid = W64 0
    · simp [hp0] at he
    · rw [if_neg hp0] at he
      cases hp : C.pages !! pid.toNat with
      | none => simp [wx0, View.ofC, hp] at he
      | some pg =>
        have hp' : (View.ofC b C).pages !! pid.toNat = some pg := hp
        simp only [wx0, hp', Option.map_some, Option.some.injEq] at he
        subst he
        have hroot : (wx0 bl t mv bv ib (View.ofC b C)).rootPid bl = ib.root' := by
          simp [WX.rootPid, wx0_bs, brec0]
        unfold WX.positions at hmem
        rw [hroot] at hmem
        have := lposF_wx0_own C b bl t mv bv ib hr0 htree _ _ pid pg hmem hp
        rw [hrt] at this
        exact ⟨pg, by first | exact hp | rfl, this, hs1, hs2⟩
  -- a bucket's cover: a bucket entry of an own leaf
  have hbkt : ∀ n s, coverW (wx0 rl t mv bv ib (View.ofC b C)) s (.bkt n) →
      ∃ L pg i, ownHas C.pages C.root L ∧ C.pages !! L = some pg ∧
        pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧ leafFlags pg i % 2 = bucketLeafFlag ∧
        n = leafKey pg i ∧ bucketHas C.pages (leafValue pg i) s := by
    intro n s hc
    obtain ⟨v, hv, -, hb⟩ := hc
    obtain ⟨L, pg, i, h1, h2, h3, h4, h5, h6, rfl⟩ :=
      rootEnts_wx0_mem C b rl t mv bv ib htree hi n v hv
    exact ⟨L, pg, i, h1, h2, h3, h4, h5, h6, hb⟩
  -- an own page covering a page `s` of a nested bucket is `s`
  have hsame : ∀ (pid : w64) pg s pgs, C.pages !! pid.toNat = some pg → C.pages !! s = some pgs →
      pid.toNat ≤ s → s < pid.toNat + (1 + pageOverflow pg) → s = pid.toNat := by
    intro pid pg s pgs hp hs h1 h2
    by_cases hne : s = pid.toNat
    · exact hne
    · rcases hdis _ _ _ _ hp hs (Ne.symm hne) with h | h <;> omega
  intro s c1 c2 h1 h2
  cases c1 with
  | pos bl1 p1 =>
    obtain ⟨rfl, pg1, hp1, ho1, a1, b1⟩ := hpos _ _ _ h1
    cases c2 with
    | pos bl2 p2 =>
      obtain ⟨rfl, pg2, hp2, ho2, a2, b2⟩ := hpos _ _ _ h2
      have : p1.toNat = p2.toNat := by
        by_cases hne : p1.toNat = p2.toNat
        · exact hne
        · rcases hdis _ _ _ _ hp1 hp2 hne with h | h <;> omega
      rw [BitVec.eq_of_toNat_eq this]
    | bkt n2 =>
      obtain ⟨L, pg, i, hL, hpg, hl, hi', hbf, -, hd⟩ := hbkt _ _ h2
      obtain ⟨pgs, hs⟩ := bucketHas_page0 hd
      have := hsame p1 pg1 s pgs hp1 hs a1 b1
      subst this
      exact (own_not_bucket C.pages hu ho1 hL hpg hl hi' hbf hd).elim
  | bkt n1 =>
    obtain ⟨L, pg, i, hL, hpg, hl, hi', hbf, hn1, hd⟩ := hbkt _ _ h1
    cases c2 with
    | pos bl2 p2 =>
      obtain ⟨rfl, pg2, hp2, ho2, a2, b2⟩ := hpos _ _ _ h2
      obtain ⟨pgs, hs⟩ := bucketHas_page0 hd
      have := hsame p2 pg2 s pgs hp2 hs a2 b2
      subst this
      exact (own_not_bucket C.pages hu ho2 hL hpg hl hi' hbf hd).elim
    | bkt n2 =>
      obtain ⟨L', pg', i', hL', hpg', hl', hi'', hbf', hn2, hd'⟩ := hbkt _ _ h2
      obtain ⟨rfl, rfl⟩ := bucket_unique C.pages hu hL hL' hpg hl hi' hbf hpg' hl' hi'' hbf' hd hd'
      rw [hpg] at hpg'; cases hpg'
      rw [hn1, hn2]

/-- `flViewU`'s parts but the cover: the MVCC rule, distinct ids below `2^62`, the view's
extents below `2^62`, the pending entries aligned. -/
theorem flViewU_parts_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (fl : FLPg) (htree : treeOK C)
    (hmv : mvccView fl (View.ofC b C)) (hwf : fl.WF) (hbl : flBelow fl C none)
    (hhwm : C.hwm ≤ 2 ^ 62) :
    mvccView fl (wx0 rl t mv bv ib (View.ofC b C)).v ∧
      fl.allIds.Nodup ∧ (∀ id ∈ fl.allIds, id.toNat < 2 ^ 62) ∧
      pagesExt (wx0 rl t mv bv ib (View.ofC b C)).v.pages ∧ pendAligned fl := by
  refine ⟨hmv, hwf.1, ?_, ?_, hwf.2.2.2.2⟩
  · intro id hid
    unfold FLPg.allIds at hid
    rcases List.mem_append.1 hid with h | h
    · exact hbl.2.2.2.2.1 id h
    · exact hbl.2.2.2.2.2 id h
  · intro id pg hpg
    have := htree.2.2.2.1 id pg hpg
    omega

/-- **`flViewU` of the initial records** (`txExcl`'s writer branch at `beginRWTx`), from what the
idle store holds of its freelist `fl` (after `ReleasePendingPages`). The cover clause and `covU`
are open: see the docstring of `flView_cover_wx0`. -/
theorem flViewU_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (fl : FLPg) (htree : treeOK C)
    (hi : Init0 C t mv bv ib)
    (hnp : ∀ s ∈ treeSlots C, s ∉ pendSlots fl)
    (hmv : mvccView fl (View.ofC b C)) (hwf : fl.WF) (hbl : flBelow fl C none)
    (hhwm : C.hwm ≤ 2 ^ 62) :
    flViewU (wx0 rl t mv bv ib (View.ofC b C)) fl := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    flViewU_parts_wx0 C b rl t mv bv ib fl htree hmv hwf hbl hhwm
  refine ⟨⟨?_, h1, h2, h3⟩, ?_, h4, h5⟩
  · -- FALSE as `lCovers` is stated (an overflow slot of a page of an unopened nested bucket is
    -- covered by the view but by no `lCovers` case: `bucketHas X.v.pages v s` takes `s` as a
    -- page id); see the report.
    sorry
  · exact covU_wx0 C b rl t mv bv ib htree hi

/-- `Tx.init`'s writer meta: one txid on, the committed state's high-water mark and root. -/
theorem initMeta_facts (C : CommitSt) (hok : C.metaOk) (h64 : C.txid + 1 < 2 ^ 64) :
    (initMeta true (metaOf (C.slot C.txid))).txid'.toNat = C.txid + 1 ∧
    (initMeta true (metaOf (C.slot C.txid))).pgid'.toNat = C.hwm ∧
    (metaOf (C.slot C.txid)).root'.root' = W64 (C.root : Int) := by
  obtain ⟨-, -, -, -, -, -, ⟨htx, hr, hpg, -⟩, -⟩ := hok
  refine ⟨?_, ?_, ?_⟩
  · simp only [initMeta, ↓reduceIte]
    rw [BitVec.toNat_add, htx]; simp; omega
  · simp only [initMeta, ↓reduceIte]; exact hpg
  · apply BitVec.eq_of_toNat_eq; rw [hr]
    have := (metaOf (C.slot C.txid)).root'.root'.isLt
    rw [hr] at this
    simp; omega

/-- **An idle writer side has no pending entry for the next writer** (`flBelow` without a live
writer: every pending transaction is committed). -/
theorem pending_next_none (fl : FLPg) (C : CommitSt) (h : flBelow fl C none) :
    fl.pending !! W64 ((C.txid + 1 : Nat) : Int) = none := by
  cases hp : fl.pending !! W64 ((C.txid + 1 : Nat) : Int) with
  | none => rfl
  | some pd =>
    rcases h.2.2.1 _ pd hp with hle | ⟨hw, -⟩
    · rw [toNat_W64_of_lt _ h.2.2.2.1] at hle; omega
    · cases hw

end winit

end bbolt
end EtcdGrove
end Perennial
