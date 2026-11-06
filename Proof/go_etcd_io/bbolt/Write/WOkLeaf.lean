/-
**`wOK` after a leaf node's entries are updated in place** (U7i, `notes/bbolt-proof-plan.md`; the
leaf-update lemmas of `Bucket.Put`/`Bucket.Delete`, and of `CreateBucket`/`DeleteBucket` at the
root bucket): `wOK_setLeaf` for any bucket, given the new entries' facts and the bucket's
`bktNested` for its new record, with the bounds `bnd` of the leaf (from `leafFor`: a fresh key is
within the leaf's bounds, not among its old keys, so `Inv/ShapeOpsLeaf.bktLocalOK_setLeaf` does
not apply); the record's other fields unchanged but `unbalanced` (`sameShapeU`, `node.del` sets
it). Corollaries for a non-root bucket's plain entries: `wOK_putLeaf` (`node.put` of a plain
entry, at the leaf `leafFor` names), `wOK_delLeaf` (`node.del`); `bm_none_nonroot` (a non-root
bucket opens no nested bucket: `leafShape`/`posShape`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.PutAt
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wokleaf
variable [GooseExts]

/-- The fields of a node record other than its entries, inodes and `unbalanced` flag. -/
def sameShapeU (r r' : NRec) : Prop :=
  r'.nv.bucket' = r.nv.bucket' ∧ r'.nv.spilled' = r.nv.spilled' ∧ r'.nv.pgid' = r.nv.pgid' ∧
  r'.nv.key' = r.nv.key' ∧ r'.nv.isLeaf' = r.nv.isLeaf' ∧ r'.nv.parent' = r.nv.parent' ∧
  r'.cs = r.cs ∧ r'.key = r.key ∧ r'.ksrc = r.ksrc ∧ r'.capOwn = r.capOwn

theorem sameShapeU_withEnts (r : NRec) (s : GoSlice) (ins : List Inode) (ws : List WEntry) :
    sameShapeU r (r.withEnts s ins ws) := by
  unfold sameShapeU NRec.withEnts; simp

theorem sameShapeU_withEntsU (r : NRec) (s : GoSlice) (ins : List Inode) (ws : List WEntry)
    (u : Bool) : sameShapeU r (r.withEntsU s ins ws u) := by
  unfold sameShapeU NRec.withEntsU; simp

/-- **A leaf's record replaced, on the bucket alone**: its clean and key facts kept (the keys
within the leaf's bounds `bnd`). -/
theorem bkt_setLeaf (v : View) (hwm : Nat) (bl l : Loc) (B : BRec) (r r' : NRec)
    (bnd : Loc → Option (List w8) × Option (List w8))
    (hc : bktClean v hwm bl B) (hk : bktKeysB v B bnd) (hr : B.ns !! l = some r)
    (hlf : r.nv.isLeaf' = true) (hsh : sameShapeU r r')
    (hins : r'.ins.length = r'.ws.length) (hsort : wsSorted r'.ws)
    (hkey : ∀ w ∈ r'.ws, 0 < w.key.length) (hlive : wsLive r'.ws)
    (hbkt : ∀ w ∈ r'.ws, isBktFlag w.flags →
      ((B.bm !! w.key).isSome = false → bvalOK v.pages hwm w.value) ∧
      (w.vs = Src.view ∨ w.vs = Src.own DFrac.discard))
    (hkeys : ∀ w ∈ r'.ws, keyIn (bnd l).1 (bnd l).2 w.key)
    (hnest : ∀ w ∈ r'.ws, isBktFlag w.flags → inBucketRoot w.value ≠ 0 → ¬ opened B w.key →
      treeKeys v.pages (inBucketRoot w.value) none none)
    (hne : r'.nv.unbalanced' = false → r'.nv.parent' ≠ null → 0 < r'.ws.length) :
    bktClean v hwm bl { B with ns := B.ns.insert l r' } ∧
      bktKeysB v { B with ns := B.ns.insert l r' } bnd := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e8, e9, e10, e11⟩ := hsh
  let B' : BRec := { B with ns := B.ns.insert l r' }
  have hnew : B'.ns !! l = some r' := GMap.lookup_insert _ _ _
  have hold : ∀ k rk, B.ns !! k = some rk → k ≠ l → B'.ns !! k = some rk := by
    intro k rk h hk; show (B.ns.insert l r') !! k = _
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact h
  have hcase : ∀ k rk, B'.ns !! k = some rk → (k = l ∧ rk = r') ∨ (k ≠ l ∧ B.ns !! k = some rk) := by
    intro k rk h
    by_cases e : k = l
    · subst e; rw [hnew] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨e, ?_⟩
      have h' : (B.ns.insert l r') !! k = some rk := h
      rwa [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h'
  have hbr : ∀ k rk, B.ns !! k = some rk → rk.nv.isLeaf' = false → k ≠ l := by
    intro k rk h hl e; subst e; rw [hr] at h; cases h; rw [hlf] at hl; cases hl
  have hpar : ∀ k rk, B.ns !! k = some rk → ∃ rk', B'.ns !! k = some rk' ∧
      rk'.nv.parent' = rk.nv.parent' ∧ rk'.nv.pgid' = rk.nv.pgid' ∧ rk'.nv.isLeaf' = rk.nv.isLeaf' := by
    intro k rk h
    by_cases e : k = l
    · subst e; rw [hr] at h; cases h; exact ⟨r', hnew, e6, e3, e5⟩
    · exact ⟨rk, hold k rk h e, rfl, rfl, rfl⟩
  have hpp : ∀ k i c, pagePosAt B' k i c ↔ pagePosAt B k i c := by
    intro k i c
    constructor
    · rintro ⟨rk, w, h, hl, hw, hwp, hnm⟩
      rcases hcase k rk h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
      · rw [e5, hlf] at hl; cases hl
      · exact ⟨rk, w, h', hl, hw, hwp, hnm⟩
    · rintro ⟨rk, w, h, hl, hw, hwp, hnm⟩
      exact ⟨rk, w, hold k rk h (hbr k rk h hl), hl, hw, hwp, hnm⟩
  have hrnn : B.bv.rootNode' ≠ null := fun h0 => by
    rw [(hc.2.2.1 h0).1] at hr; simp at hr
  have hn := hc.2.2.2.2.2.2.2.1
  have hclean : ∀ k rk, B'.ns !! k = some rk → nodeClean v hwm bl B' k rk := by
    intro k rk h
    rcases hcase k rk h with ⟨rfl, rfl⟩ | ⟨hkl, h'⟩
    · obtain ⟨h1, h2, -, -, -, -, h7, h8, h9, h10, h11, -, -, h14, h15, h16, h17⟩ := hn k r hr
      refine ⟨e1 ▸ h1, e11 ▸ h2, hins, hsort, hkey, hlive, e2 ▸ h7, e3 ▸ h8,
        fun h0 => e3 ▸ h9 h0, fun h0 => e3 ▸ h10 h0, ?_, fun _ w hw hf => hbkt w hw hf, ?_,
        fun h0 => h14 (e6 ▸ h0), ?_, e8 ▸ h16, ?_⟩
      · rw [e4, e9, e10]; exact h11
      · intro h0; rw [e5, hlf] at h0; cases h0
      · intro h0
        obtain ⟨rp, hrp, hrpl, hin, w, hw, hwp⟩ := h15 (e6 ▸ h0)
        rw [e6]
        exact ⟨rp, hold _ rp hrp (hbr _ rp hrp hrpl), hrpl, hin, w, hw, hwp.trans e3.symm⟩
      · intro c hcs
        rw [e8] at hcs
        obtain ⟨rc, hrc, hrcp⟩ := h17 c hcs
        obtain ⟨rc', hrc', hp, -, -⟩ := hpar c rc hrc
        exact ⟨rc', hrc', hp.trans hrcp⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
        hn k rk h'
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ?_, h14, ?_, h16, ?_⟩
      · intro h0
        obtain ⟨a1, a2, a3⟩ := h13 h0
        refine ⟨a1, a2, fun w hw => ?_⟩
        obtain ⟨b1, b2, b3⟩ := a3 w hw
        refine ⟨b1, fun l' hl' => ?_, b3⟩
        obtain ⟨r2, hr2, hp2⟩ := b2 l' hl'
        obtain ⟨r2', hr2', hp, -, -⟩ := hpar l' r2 hr2
        exact ⟨r2', hr2', hp.trans hp2⟩
      · intro h0
        obtain ⟨rp, hrp, hrpl, hin, w, hw, hwp⟩ := h15 h0
        exact ⟨rp, hold _ rp hrp (hbr _ rp hrp hrpl), hrpl, hin, w, hw, hwp⟩
      · intro c hcs
        obtain ⟨rc, hrc, hrcp⟩ := h17 c hcs
        obtain ⟨rc', hrc', hp, -, -⟩ := hpar c rc hrc
        exact ⟨rc', hrc', hp.trans hrcp⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, c9, c10, c11⟩ := hc
    refine ⟨c1, c2, fun h0 => absurd h0 hrnn, c4, ?_, c6, ?_, hclean, ?_, ?_, c11⟩
    · intro c l' h
      obtain ⟨hl', r2, hr2, hp2⟩ := c5 c l' h
      obtain ⟨r2', hr2', -, hp, -⟩ := hpar l' r2 hr2
      exact ⟨hl', r2', hr2', hp.trans hp2⟩
    · intro h0 k rk h
      rcases hcase k rk h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
      · rw [e5]; exact hlf
      · exact c7 h0 k rk h'
    · intro l1 i1 c1' l2 i2 c2' h1 h2 hne d
      exact c9 l1 i1 c1' l2 i2 c2' ((hpp _ _ _).1 h1) ((hpp _ _ _).1 h2) hne d
    · intro k i c h d
      exact c10 k i c ((hpp _ _ _).1 h) d
  · obtain ⟨k1, k2, k3⟩ := hk
    refine ⟨k1, fun rk h => ?_, fun k rk h => ?_⟩
    · rcases hcase _ rk h with ⟨e, rfl⟩ | ⟨-, h'⟩
      · rw [e6]; exact k2 r (e ▸ hr)
      · exact k2 rk h'
    · rcases hcase k rk h with ⟨rfl, rfl⟩ | ⟨hkl, h'⟩
      · obtain ⟨n1, n2, n3, -, n5, -⟩ := k3 k r hr
        refine ⟨hkeys, fun h0 => n2 (e6 ▸ h0), fun h0 => ?_, fun h0 => ?_,
          fun _ hu hp => hne hu hp, fun _ w hw hf => hnest w hw hf⟩
        · obtain ⟨hkn, rp, i, w, hrp, hw, hwp, hwk, hb⟩ := n3 (e6 ▸ h0)
          have hrpl := (hn k r hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (e6 ▸ h0)
          obtain ⟨rp', hrp', hrpl', -⟩ := hrpl
          rw [hrp] at hrp'; cases hrp'
          refine ⟨e4 ▸ hkn, rp, i, w, ?_, hw, hwp.trans e3.symm, hwk.trans e9.symm, ?_⟩
          · rw [e6]; exact hold _ rp hrp (hbr _ rp hrp hrpl')
          · rw [e6]; exact hb
        · rw [e5, hlf] at h0; cases h0
      · obtain ⟨n1, n2, n3, n4, n5, n6⟩ := k3 k rk h'
        refine ⟨n1, n2, fun h0 => ?_, fun h0 => ?_, n5, n6⟩
        · obtain ⟨hkn, rp, i, w, hrp, hw, hwp, hwk, hb⟩ := n3 h0
          obtain ⟨rp', hrp', hrpl', -⟩ := (hn k rk h').2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0
          rw [hrp] at hrp'; cases hrp'
          exact ⟨hkn, rp, i, w, hold _ rp hrp (hbr _ rp hrp hrpl'), hw, hwp, hwk, hb⟩
        · obtain ⟨a1, kind, a2⟩ := n4 h0
          refine ⟨a1, kind, fun i w hw => ⟨fun l' hl' => ?_, (a2 i w hw).2⟩⟩
          obtain ⟨r2, hr2, hk2⟩ := (a2 i w hw).1 l' hl'
          obtain ⟨r2', hr2', -, -, hl2⟩ := hpar l' r2 hr2
          exact ⟨r2', hr2', hl2.trans hk2⟩

/-- `setNode` of an existing bucket is `setNodeT`. -/
theorem setNode_eqT (X : WX) (bl l : Loc) (B : BRec) (r' : NRec) (hB : X.t.bs !! bl = some B) :
    X.setNode bl l r' = { X with t := X.t.setNodeT bl l B r' } := by
  unfold WX.setNode WX.setBkt WTx.setNodeT
  rw [hB]

/-- **`wOK` after a leaf's record is replaced** (see the module doc). -/
theorem wOK_setLeaf (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (bnd : Loc → Option (List w8) × Option (List w8))
    (hok : wOK X) (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (hlf : r.nv.isLeaf' = true) (hsh : sameShapeU r r') (hbk : bktKeysB X.v B bnd)
    (hins : r'.ins.length = r'.ws.length) (hsort : wsSorted r'.ws) (hlive : wsLive r'.ws)
    (hent : ∀ w ∈ r'.ws, 0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax ∧
      (bl = X.rl → w.key.length ≤ maxKeySize))
    (hshape : ∀ w ∈ r'.ws, (isBktFlag w.flags ↔ bl = X.rl))
    (hbkt : ∀ w ∈ r'.ws, isBktFlag w.flags →
      ((B.bm !! w.key).isSome = false → bvalOK X.v.pages X.t.mv.pgid'.toNat w.value) ∧
      (w.vs = Src.view ∨ w.vs = Src.own DFrac.discard))
    (hkeys : ∀ w ∈ r'.ws, keyIn (bnd l).1 (bnd l).2 w.key)
    (hnest : ∀ w ∈ r'.ws, isBktFlag w.flags → inBucketRoot w.value ≠ 0 → ¬ opened B w.key →
      treeKeys X.v.pages (inBucketRoot w.value) none none)
    (hpg : ∀ w ∈ r'.ws, w.pgid = W64 0)
    (hne : r'.nv.unbalanced' = false → r'.nv.parent' ≠ null → 0 < r'.ws.length)
    (hnst : bktNested X.v (X.t.setNodeT bl l B r') { B with ns := B.ns.insert l r' }) :
    wOK (X.setNode bl l r') := by
  rw [setNode_eqT X bl l B r' hB]
  obtain ⟨⟨hw, ⟨hpm, hbufs, hls, hps, hrni⟩, h2, htx, hrlS, hall⟩, hkn, htp, heb, hho, hlo, hnl,
    hvw⟩ := hok
  let B' : BRec := { B with ns := B.ns.insert l r' }
  have hbs : ∀ c C, (X.t.bs.insert bl B') !! c = some C →
      (c = bl ∧ C = B') ∨ (c ≠ bl ∧ X.t.bs !! c = some C) := by
    intro c C h
    by_cases e : c = bl
    · subst e; rw [GMap.lookup_insert] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr ⟨e, h⟩
  have hsome : ∀ c, ((X.t.bs.insert bl B') !! c).isSome = (X.t.bs !! c).isSome := by
    intro c
    by_cases e : c = bl
    · subst e; rw [GMap.lookup_insert, hB]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]
  have hns : ∀ k rk, B'.ns !! k = some rk → (k = l ∧ rk = r') ∨ (k ≠ l ∧ B.ns !! k = some rk) := by
    intro k rk h
    by_cases e : k = l
    · subst e
      have : (B.ns.insert k r') !! k = some r' := GMap.lookup_insert _ _ _
      have h' : (B.ns.insert k r') !! k = some rk := h
      rw [this] at h'; cases h'; exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨e, ?_⟩
      have h' : (B.ns.insert l r') !! k = some rk := h
      rwa [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h'
  obtain ⟨e1, e2, e3, e4, e5, e6, e8, e9, e10, e11⟩ := hsh
  have hcB := (hall bl B hB).1
  obtain ⟨hcB', hkB'⟩ := bkt_setLeaf X.v X.t.mv.pgid'.toNat bl l B r r' bnd hcB hbk hr hlf
    ⟨e1, e2, e3, e4, e5, e6, e8, e9, e10, e11⟩ hins hsort (fun w hw => (hent w hw).1) hlive hbkt
    hkeys hnest hne
  -- page positions are unchanged
  have hbr : ∀ k rk, B.ns !! k = some rk → rk.nv.isLeaf' = false → k ≠ l := by
    intro k rk h hl e; subst e; rw [hr] at h; cases h; rw [hlf] at hl; cases hl
  have hpp : ∀ k i c, pagePosAt B' k i c ↔ pagePosAt B k i c := by
    intro k i c
    constructor
    · rintro ⟨rk, w, h, hl, hw, hwp, hnm⟩
      rcases hns k rk h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
      · rw [e5, hlf] at hl; cases hl
      · exact ⟨rk, w, h', hl, hw, hwp, hnm⟩
    · rintro ⟨rk, w, h, hl, hw, hwp, hnm⟩
      have hkl := hbr k rk h hl
      refine ⟨rk, w, ?_, hl, hw, hwp, hnm⟩
      show (B.ns.insert l r') !! k = _
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hkl)]; exact h
  have hposR : ∀ c, posRoot B' c ↔ posRoot B c := by
    intro c; unfold posRoot
    constructor
    · rintro (h | ⟨k, i, h, hc⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, i, (hpp _ _ _).1 h, hc⟩
    · rintro (h | ⟨k, i, h, hc⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, i, (hpp _ _ _).2 h, hc⟩
  have hobjs : (X.t.setNodeT bl l B r').objs = X.t.objs.insert l (.node bl r') :=
    objs_setNodeT X.t bl l B r r' hd hB hr
  have hbobjs : (X.t.setNodeT bl l B r').bobjs = X.t.bobjs.insert bl B' :=
    bobjs_setNodeT X.t bl l B r'
  refine ⟨⟨hw, ⟨hpm, hbufs, ?_, ?_, ?_⟩, h2, htx, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hvw⟩
  · -- leafShape
    intro c C hC k rk hk hl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
    · rcases hns k rk hk with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
      · exact hshape
      · exact hls c B hB k rk hk' hl
    · exact hls c C hC' k rk hk hl
  · -- posShape
    intro c C hC cc p pg hpr hown hpg' hfl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
    · exact hps c B hB cc p pg ((hposR cc).1 hpr) hown hpg' hfl
    · exact hps c C hC' cc p pg hpr hown hpg' hfl
  · -- rootNotInline
    intro C hC
    rcases hbs X.rl C hC with ⟨e, rfl⟩ | ⟨-, hC'⟩
    · exact hrni B (e ▸ hB)
    · exact hrni C hC'
  · show ((X.t.bs.insert bl B') !! X.rl).isSome
    rw [hsome]; exact hrlS
  · intro c C hC
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
    · refine ⟨hcB', fun name c' h => ?_⟩
      show ((X.t.bs.insert c B') !! c').isSome
      rw [hsome]; exact (hall c B hB).2 name c' h
    · refine ⟨(hall c C hC').1, fun name c' h => ?_⟩
      show ((X.t.bs.insert bl B') !! c').isSome
      rw [hsome]; exact (hall c C hC').2 name c' h
  · -- keys and nested buckets
    intro c C hC
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hcb, hC'⟩
    · exact ⟨⟨bnd, hkB'⟩, hnst⟩
    · refine ⟨(hkn c C hC').1, fun k c' hk => ?_⟩
      obtain ⟨C0, v, hC0, hin, h16, hinl, hib, hib2, hipg⟩ := (hkn c C hC').2 k c' hk
      refine ⟨if c' = bl then B' else C0, v, ?_, hin, h16, hinl, ?_⟩
      · show (X.t.bs.insert bl B') !! c' = _
        by_cases e : c' = bl
        · subst e; rw [GMap.lookup_insert, if_pos rfl]
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), if_neg e]; exact hC0
      · by_cases e : c' = bl
        · subst e; rw [hB] at hC0; cases hC0; rw [if_pos rfl]; exact ⟨hib, hib2, hipg⟩
        · rw [if_neg e]; exact ⟨hib, hib2, hipg⟩
  · -- txPg
    intro c C hC k rk hk
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
    · rcases hns k rk hk with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
      · obtain ⟨hp1, -⟩ := htp c B hB k r hr
        refine ⟨fun _ => ⟨hpg, fun h0 => ?_⟩, fun h0 => ?_⟩
        · rw [e3]; exact (hp1 hlf).2 h0
        · rw [e5, hlf] at h0; cases h0
      · exact htp c B hB k rk hk'
    · exact htp c C hC' k rk hk
  · -- entriesBounded
    intro c C hC k rk hk
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
    · rcases hns k rk hk with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
      · exact hent
      · exact heb c B hB k rk hk'
    · exact heb c C hC' k rk hk
  · -- handlesOK
    intro b nm hb
    show ((X.t.setNodeT bl l B r').bobjs !! b).isSome
    rw [hbobjs]
    by_cases e : b = bl
    · subst e; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hho b nm hb
  · -- liveOK
    obtain ⟨l1, l2, l3, l4, l5⟩ := hlo
    refine ⟨l1, fun k hk => ?_, fun c C hC => ?_, fun c C k rk hC hk => ?_, l5⟩
    · show ((X.t.setNodeT bl l B r').objs !! k).isSome
      rw [hobjs]
      by_cases e : k = l
      · subst e; rw [GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact l2 k hk
    · rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
      · exact l3 c B hB
      · exact l3 c C hC'
    · rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨-, hC'⟩
      · rcases hns k rk hk with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
        · exact l4 c B k r hB hr
        · exact l4 c B k rk hB hk'
      · exact l4 c C k rk hC' hk
  · -- nlocOK
    intro n b p hn hl
    obtain ⟨B0, r0, hB0, hr0, hp⟩ := hnl n b p hn hl
    by_cases e : b = bl
    · subst e
      obtain rfl : B0 = B := (Option.some.inj (hB0.symm.trans hB))
      refine ⟨B', if n = l then r' else r0, GMap.lookup_insert _ _ _, ?_, ?_⟩
      · show (B0.ns.insert l r') !! n = _
        by_cases e' : n = l
        · subst e'; rw [GMap.lookup_insert, if_pos rfl]
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e'), if_neg e']; exact hr0
      · by_cases e' : n = l
        · subst e'; rw [hr] at hr0; cases hr0; rw [if_pos rfl, e3]; exact hp
        · rw [if_neg e']; exact hp
    · refine ⟨B0, r0, ?_, hr0, hp⟩
      show (X.t.bs.insert bl B') !! b = _
      rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hB0

/-- **A non-root bucket opens no nested bucket** (its leaves and the pages under its positions
hold plain entries only: `leafShape`, `posShape`). -/
theorem bm_none_nonroot (X : WX) (bl : Loc) (B : BRec) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) (hroot : bl ≠ X.rl) : ∀ k, B.bm !! k = none := by
  intro k
  cases hk : B.bm !! k with
  | none => rfl
  | some c =>
    exfalso
    obtain ⟨C, v, -, hin, -⟩ := (hok.2.1 bl B hB).2 k c hk
    rcases hin with ⟨l, r, w, hr, hl, hw, -, hf, -⟩ | ⟨cc, p, pg, i, hpr, hown, hpg, hfl, hi, -, hbf, -⟩
    · exact hroot ((hok.1.2.1.2.2.1 bl B hB l r hr hl w hw).1 hf)
    · exact hroot (((hok.1.2.1.2.2.2.1 bl B hB cc p pg hpr hown hpg hfl i hi).1).1 hbf)

/-- With no nested bucket opened, `bktNested` holds. -/
theorem bktNested_of_bm_none (v : View) (T : WTx) (B : BRec) (h : ∀ k, B.bm !! k = none) :
    bktNested v T B := by
  intro k c hk; rw [h k] at hk; cases hk

/-! ### Entries' lists -/

omit [GooseExts] in
theorem mem_wsPutAt' {ws : List WEntry} {k : List w8} {e w : WEntry} (h : w ∈ wsPutAt ws k e) :
    w ∈ ws ∨ w = e := by
  unfold wsPutAt at h
  split at h <;>
  · simp only [List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact Or.inl (List.mem_of_mem_take h)
    · exact Or.inr h
    · exact Or.inl (List.mem_of_mem_drop h)

omit [GooseExts] in
theorem wsDelAt_sublist (ws : List WEntry) (k : List w8) : (wsDelAt ws k).Sublist ws := by
  unfold wsDelAt
  split
  · rw [← List.eraseIdx_eq_take_drop_succ]; exact List.eraseIdx_sublist _ _
  · exact List.Sublist.refl _

omit [GooseExts] in
theorem wsSorted_of_pw (ws : List WEntry) (h : wsPw ws) : wsSorted ws := by
  intro i j hij hj
  unfold wsPw at h
  rw [List.pairwise_iff_getElem] at h
  unfold wKey
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj]
  exact h i j (by omega) hj hij

theorem wsPw_wsPut (ws : List WEntry) (e : WEntry) (h : wsPw ws) : wsPw (wsPut ws e) := by
  unfold wsPw at h ⊢
  rw [wsPut_split, List.pairwise_append, List.pairwise_cons]
  refine ⟨h.sublist List.filter_sublist, ⟨fun a ha => by simpa using (List.mem_filter.1 ha).2,
    h.sublist List.filter_sublist⟩, fun a ha b hb => ?_⟩
  have ha' : go.GoStringLt a.key e.key := by simpa using (List.mem_filter.1 ha).2
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ha'
  · exact go.goStringLt_trans ha' (by simpa using (List.mem_filter.1 hb).2)

/-- **A plain entry put into a non-root bucket's leaf `leafFor` names** (`Bucket.Put`'s
`node.put`): `wOK` kept. -/
theorem wOK_putLeaf (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (k : List w8) (e : WEntry)
    (s : GoSlice) (ins : List Inode)
    (hok : wOK X) (hd : objsDisj X.t) (hroot : bl ≠ X.rl) (hlf : leafFor X bl k l)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (hek : e.key = k) (hk : 0 < k.length) (hbnd : k.length + e.value.length ≤ bboltEntryMax)
    (hfl : ¬ isBktFlag e.flags) (hpg : e.pgid = W64 0) (hks : e.ks ≠ Src.stale)
    (hvs : e.vs ≠ Src.stale) (hins : ins.length = (wsPutAt r.ws k e).length) :
    wOK (X.setNode bl l (r.withEnts s ins (wsPutAt r.ws k e))) := by
  obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, hbk, hkin⟩ := hlf
  obtain rfl : B0 = B := (Option.some.inj (hB0.symm.trans hB))
  obtain rfl : r0 = r := (Option.some.inj (hr0.symm.trans hr))
  have hcl := ((hok.1.2.2.2.2.2 bl B0 hB).1).2.2.2.2.2.2.2.1 l r0 hr
  have hpw : wsPw r0.ws := wsSorted_pw _ hcl.2.2.2.1
  have hput : wsPutAt r0.ws k e = wsPut r0.ws e := by rw [← hek]; exact wsPutAt_wsPut _ _ hpw
  have hplain : ∀ w ∈ r0.ws, ¬ isBktFlag w.flags := fun w hw hf =>
    hroot ((hok.1.2.1.2.2.1 bl B0 hB l r0 hr hlf0 w hw).1 hf)
  have hmem := fun w (hw : w ∈ (r0.withEnts s ins (wsPutAt r0.ws k e)).ws) =>
    mem_wsPutAt' (show w ∈ wsPutAt r0.ws k e from hw)
  have hnp : ∀ w ∈ (r0.withEnts s ins (wsPutAt r0.ws k e)).ws, ¬ isBktFlag w.flags := by
    intro w hw
    rcases hmem w hw with h | rfl
    · exact hplain w h
    · exact hfl
  apply wOK_setLeaf X bl l B0 r0 _ bnd hok hd hB hr hlf0 (sameShapeU_withEnts r0 s ins _) hbk
  · exact hins
  · show wsSorted (wsPutAt r0.ws k e)
    rw [hput]; exact wsSorted_of_pw _ (wsPw_wsPut _ _ hpw)
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact hcl.2.2.2.2.2.1 w h
    · exact ⟨hks, hvs⟩
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact (hok.2.2.2.1 bl B0 hB l r0 hr w h)
    · exact ⟨hek ▸ hk, hek ▸ hbnd, fun h => absurd h hroot⟩
  · intro w hw
    exact ⟨fun h => absurd h (hnp w hw), fun h => absurd h hroot⟩
  · intro w hw h; exact absurd h (hnp w hw)
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact (hbk.2.2 l r0 hr).1 w h
    · rw [hek]; exact hkin
  · intro w hw h; exact absurd h (hnp w hw)
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact ((hok.2.2.1 bl B0 hB l r0 hr).1 hlf0).1 w h
    · exact hpg
  · intro _ _
    show 0 < (wsPutAt r0.ws k e).length
    rw [hput, wsPut_split]; simp only [List.length_append, List.length_cons]; omega
  · exact bktNested_of_bm_none _ _ _ (bm_none_nonroot X bl B0 hok hB hroot)

/-- **An entry deleted from a non-root bucket's leaf** (`Bucket.Delete`'s `node.del`): `wOK`
kept. -/
theorem wOK_delLeaf (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (k : List w8)
    (s : GoSlice) (ins : List Inode)
    (hok : wOK X) (hd : objsDisj X.t) (hroot : bl ≠ X.rl)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hlf : r.nv.isLeaf' = true)
    (hins : ins.length = (wsDelAt r.ws k).length) :
    wOK (X.setNode bl l (r.withEntsU s ins (wsDelAt r.ws k) true)) := by
  obtain ⟨bnd, hbk⟩ := (hok.2.1 bl B hB).1
  have hcl := ((hok.1.2.2.2.2.2 bl B hB).1).2.2.2.2.2.2.2.1 l r hr
  have hsub := wsDelAt_sublist r.ws k
  have hmem : ∀ w ∈ (r.withEntsU s ins (wsDelAt r.ws k) true).ws, w ∈ r.ws :=
    fun w hw => hsub.subset hw
  have hplain : ∀ w ∈ (r.withEntsU s ins (wsDelAt r.ws k) true).ws, ¬ isBktFlag w.flags :=
    fun w hw hf => hroot ((hok.1.2.1.2.2.1 bl B hB l r hr hlf w (hmem w hw)).1 hf)
  apply wOK_setLeaf X bl l B r _ bnd hok hd hB hr hlf (sameShapeU_withEntsU r s ins _ true) hbk
  · exact hins
  · show wsSorted (wsDelAt r.ws k)
    exact wsSorted_of_pw _ ((wsSorted_pw _ hcl.2.2.2.1).sublist hsub)
  · intro w hw; exact hcl.2.2.2.2.2.1 w (hmem w hw)
  · intro w hw; exact hok.2.2.2.1 bl B hB l r hr w (hmem w hw)
  · intro w hw
    exact ⟨fun h => absurd h (hplain w hw), fun h => absurd h hroot⟩
  · intro w hw h; exact absurd h (hplain w hw)
  · intro w hw; exact (hbk.2.2 l r hr).1 w (hmem w hw)
  · intro w hw h; exact absurd h (hplain w hw)
  · intro w hw; exact ((hok.2.2.1 bl B hB l r hr).1 hlf).1 w (hmem w hw)
  · intro h; cases h
  · exact bktNested_of_bm_none _ _ _ (bm_none_nonroot X bl B hok hB hroot)

end wokleaf

end Write

end bbolt
end EtcdGrove
end Perennial
