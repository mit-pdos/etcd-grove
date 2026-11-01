/-
`Bucket.spill`: a bucket's record up to its slices' sources (`spBSim`): the same buckets,
nodes and entries, only where the bytes are (a remap's `dereference` copies them, the spill
persists nested buckets' values). What the spill needs of a bucket (`bktClean`, its keys,
nested buckets, tokens, ...) carries over, given what the new sources are.
-/
module

public import Proof.go_etcd_io.bbolt.SpillBucketLemmas
public import Proof.go_etcd_io.bbolt.SpillTree
public import Proof.go_etcd_io.bbolt.RebalanceFrame

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- An entry without its sources. -/
def spStrip (w : WEntry) : w32 × w64 × List w8 × List w8 := (w.flags, w.pgid, w.key, w.value)

/-- The record `r'` is `r` but for its slices and their sources. -/
def spREq (r r' : NRec) : Prop :=
  r'.ws.map spStrip = r.ws.map spStrip ∧ r'.cs = r.cs ∧ r'.ins.length = r.ins.length ∧
  r'.key = r.key ∧ r'.nv.bucket' = r.nv.bucket' ∧ r'.nv.isLeaf' = r.nv.isLeaf' ∧
  r'.nv.spilled' = r.nv.spilled' ∧ r'.nv.unbalanced' = r.nv.unbalanced' ∧
  r'.nv.pgid' = r.nv.pgid' ∧ r'.nv.parent' = r.nv.parent' ∧
  (r'.nv.key' = slice.nil ↔ r.nv.key' = slice.nil)

/-- `B'` is `B` with node records related by `spREq`. -/
def spBSim (B B' : BRec) : Prop :=
  B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧ B'.ipg = B.ipg ∧
  (∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧ spREq ry ry') ∧
  (∀ y ry', B'.ns !! y = some ry' → ∃ ry, B.ns !! y = some ry ∧ spREq ry ry')

theorem spREq_refl (r : NRec) : spREq r r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩

theorem spREq_trans {r1 r2 r3 : NRec} (h1 : spREq r1 r2) (h2 : spREq r2 r3) : spREq r1 r3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, i1, j1, k1, l1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, i2, j2, k2, l2⟩ := h2
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1,
    g2.trans g1, i2.trans i1, j2.trans j1, k2.trans k1, l2.trans l1⟩

theorem spBSim_refl (B : BRec) : spBSim B B :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ r h => ⟨r, h, spREq_refl r⟩, fun _ r h => ⟨r, h, spREq_refl r⟩⟩

theorem spBSim_trans {B1 B2 B3 : BRec} (h1 : spBSim B1 B2) (h2 : spBSim B2 B3) : spBSim B1 B3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, fun y r h => ?_,
    fun y r h => ?_⟩
  · obtain ⟨r2, h2', e⟩ := f1 y r h
    obtain ⟨r3, h3, e'⟩ := f2 y r2 h2'
    exact ⟨r3, h3, spREq_trans e e'⟩
  · obtain ⟨r2, h2', e⟩ := g2 y r h
    obtain ⟨r1, h1', e'⟩ := g1 y r2 h2'
    exact ⟨r1, h1', spREq_trans e' e⟩

/-- An entry of `r'.ws` is an entry of `r.ws` up to its sources. -/
theorem spMem_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip) (w' : WEntry)
    (hw : w' ∈ ws') : ∃ w ∈ ws, spStrip w = spStrip w' := by
  have : spStrip w' ∈ ws.map spStrip := by rw [← h]; exact List.mem_map_of_mem hw
  obtain ⟨w, hw, e⟩ := List.mem_map.1 this
  exact ⟨w, hw, e⟩

theorem spGet_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip) (i : Nat)
    (w' : WEntry) (hw : ws'[i]? = some w') : ∃ w, ws[i]? = some w ∧ spStrip w = spStrip w' := by
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, hw, Option.map_some] at e
  cases h2 : ws[i]? with
  | none => rw [h2] at e; cases e
  | some w => rw [h2] at e; exact ⟨w, rfl, (Option.some.inj e).symm⟩

theorem spGet_strip' {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip) (i : Nat)
    (w : WEntry) (hw : ws[i]? = some w) : ∃ w', ws'[i]? = some w' ∧ spStrip w = spStrip w' := by
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, hw, Option.map_some] at e
  cases h2 : ws'[i]? with
  | none => rw [h2] at e; cases e
  | some w' => rw [h2] at e; exact ⟨w', rfl, (Option.some.inj e).symm⟩

theorem spStrip_eq {w w' : WEntry} (h : spStrip w = spStrip w') :
    w.flags = w'.flags ∧ w.pgid = w'.pgid ∧ w.key = w'.key ∧ w.value = w'.value := by
  unfold spStrip at h; simp only [Prod.mk.injEq] at h; exact h

theorem spLen_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip) :
    ws'.length = ws.length := by
  have := congrArg List.length h; simpa using this

theorem spKeys_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip) :
    ws'.map WEntry.key = ws.map WEntry.key := by
  have := congrArg (List.map (fun x : w32 × w64 × List w8 × List w8 => x.2.2.1)) h
  simpa [List.map_map, spStrip, Function.comp_def] using this

theorem spPgids_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip) :
    ws'.map WEntry.pgid = ws.map WEntry.pgid := by
  have := congrArg (List.map (fun x : w32 × w64 × List w8 × List w8 => x.2.1)) h
  simpa [List.map_map, spStrip, Function.comp_def] using this

theorem spWKey_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip) (i : Nat) :
    wKey ws' i = wKey ws i := by
  unfold wKey
  have hk := spKeys_strip h
  have e := congrArg (fun l => l[i]?) hk
  simp only [List.getElem?_map] at e
  rw [e]

theorem spSorted_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip)
    (hs : wsSorted ws) : wsSorted ws' := by
  intro i j hij hj
  rw [spWKey_strip h, spWKey_strip h]
  exact hs i j hij (by rw [← spLen_strip h]; exact hj)

theorem spEntryBnd_strip {ws ws' : List WEntry} (h : ws'.map spStrip = ws.map spStrip)
    (b : Option (List w8) × Option (List w8)) (i : Nat) : entryBnd b ws' i = entryBnd b ws i := by
  unfold entryBnd
  rw [spLen_strip h]
  congr 1
  · unfold childLo; split <;> simp [spWKey_strip h]
  · unfold childHi; split <;> simp [spWKey_strip h]

theorem pagePosAt_ss {B B' : BRec} (h : spBSim B B') (l : Loc) (i : Nat) (c : w64) :
    pagePosAt B' l i c ↔ pagePosAt B l i c := by
  obtain ⟨-, -, hnm, -, -, hf, hb⟩ := h
  constructor
  · rintro ⟨r', w', hr', hbr, hw, hc, hn⟩
    obtain ⟨r, hr, e⟩ := hb l r' hr'
    obtain ⟨w, hw0, ew⟩ := spGet_strip e.1 i w' hw
    exact ⟨r, w, hr, by rw [← e.2.2.2.2.2.1]; exact hbr, hw0, by rw [(spStrip_eq ew).2.1]; exact hc,
      by rw [← hnm]; exact hn⟩
  · rintro ⟨r, w, hr, hbr, hw, hc, hn⟩
    obtain ⟨r', hr', e⟩ := hf l r hr
    obtain ⟨w', hw', ew⟩ := spGet_strip' e.1 i w hw
    exact ⟨r', w', hr', by rw [e.2.2.2.2.2.1]; exact hbr, hw', by rw [← (spStrip_eq ew).2.1]; exact hc,
      by rw [hnm]; exact hn⟩

/-- A well-formed tree stays one with a higher high-water mark. -/
theorem spTreeWF_mono (P : GMap Nat (List w8)) (h h' x : Nat) (hw : treeWF P h x) (hle : h ≤ h') :
    treeWF P h' x :=
  treeWF_transfer P P h h' x hw (fun y hy => ⟨rfl, by have := treeWF_lt P h x y hw hy; omega⟩)

theorem spBvalOK_mono (P : GMap Nat (List w8)) (h h' : Nat) (v : List w8) (hv : bvalOK P h v)
    (hle : h ≤ h') : bvalOK P h' v := by
  obtain ⟨hb, hi⟩ := hv
  refine ⟨?_, hi⟩
  cases hb with
  | file _ h16 h0 ht => exact bucketWF.file _ h16 h0 (spTreeWF_mono P h h' _ ht hle)
  | inline _ h16 h0 hf hp =>
    refine bucketWF.inline _ h16 h0 hf ?_
    obtain ⟨-, -, hwf, -, hflg⟩ := hi h0
    refine pageTreeWF.leaf _ _ hf hwf (fun j hj hb => ?_)
    have := (hflg j hj).2
    rw [this] at hb
    exact absurd hb (by unfold bucketLeafFlag; decide)

variable (W : WView) (hwm : Nat) (bl : Loc)

/-- `bktClean` carries over to a record up to its sources, with a higher high-water mark, the new
sources live and nested buckets' values persistent. -/
theorem bktClean_ss {B B' : BRec} (h : spBSim B B') (hc : bktClean W hwm bl B) (hwm' : Nat)
    (hle : hwm ≤ hwm')
    (hisrc : B.ib.root' = W64 0 → B.bv.rootNode' = null →
      B'.isrc = Src.view ∨ B'.isrc = Src.own DFrac.discard)
    (hlive : ∀ l r', B'.ns !! l = some r' → wsLive r'.ws ∧ (r'.nv.key' ≠ slice.nil → r'.ksrc ≠ Src.stale))
    (hvs : ∀ l r', B'.ns !! l = some r' → r'.nv.isLeaf' = true → ∀ w ∈ r'.ws, isBktFlag w.flags →
      w.vs = Src.view ∨ w.vs = Src.own DFrac.discard) :
    bktClean W hwm' bl B' := by
  have hpos := pagePosAt_ss h
  obtain ⟨hbv, hib, hnm, hbm, hipg, hf, hb⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0 hn
    rw [hib] at h0; rw [hbv] at hn
    obtain ⟨a, -, b⟩ := c1 h0 hn
    exact ⟨by rw [hbv]; exact a, hisrc h0 hn, by rw [hipg]; exact b⟩
  · intro h0
    rw [hib] at h0 ⊢; rw [hbv]
    obtain ⟨a, b⟩ := c2 h0
    exact ⟨by omega, fun hn => spTreeWF_mono _ _ _ _ (b hn) hle⟩
  · intro h0
    rw [hbv] at h0
    obtain ⟨hns, hnm0⟩ := c3 h0
    refine ⟨?_, by rw [hnm]; exact hnm0⟩
    apply GMap.ext; intro y
    cases hy : B'.ns !! y with
    | none => show none = (∅ : GMap Loc NRec) !! y; simp
    | some ry' =>
      obtain ⟨ry, hry, -⟩ := hb y ry' hy
      rw [hns] at hry; simp at hry
  · rw [hbv, hnm, hib]; exact c4
  · intro c l hl
    rw [hnm] at hl
    obtain ⟨hnn, r, hr, hp⟩ := c5 c l hl
    obtain ⟨r', hr', e⟩ := hf l r hr
    exact ⟨hnn, r', hr', by rw [e.2.2.2.2.2.2.2.2.1]; exact hp⟩
  · rw [hib, hbv]; exact c6
  · intro h0 l r' hr'
    rw [hib] at h0
    obtain ⟨r, hr, e⟩ := hb l r' hr'
    rw [e.2.2.2.2.2.1]; exact c7 h0 l r hr
  · intro l r' hr'
    obtain ⟨r, hr, e⟩ := hb l r' hr'
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := e
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := c8 l r hr
    obtain ⟨hl1, hl2⟩ := hlive l r' hr'
    refine ⟨by rw [q5]; exact n1, by rw [q3, spLen_strip q1]; exact n2, spSorted_strip q1 n3,
      fun w hw => ?_, hl1, by rw [q7]; exact n6,
      by rw [hnm, q9]; exact n7, by rw [hib, q9]; exact n8,
      fun h0 => by rw [hib] at h0; rw [q9]; exact spTreeWF_mono _ _ _ _ (n9 h0) hle, ?_, ?_, ?_,
      by rw [q10, hbv]; exact n13, ?_, by rw [q2]; exact n15, ?_⟩
    · obtain ⟨w0, hw0, e⟩ := spMem_strip q1 w hw
      rw [← (spStrip_eq e).2.2.1]; exact n4 w0 hw0
    · by_cases hk : r'.nv.key' = slice.nil
      · exact Or.inl hk
      · right
        have hk0 : r.nv.key' ≠ slice.nil := fun h0 => hk (q11.2 h0)
        rcases n10 with h | ⟨hl, -⟩
        · exact absurd h hk0
        · exact ⟨by rw [q4]; exact hl, hl2 hk⟩
    · intro hl w hw hbk
      rw [q6] at hl
      obtain ⟨w0, hw0, e⟩ := spMem_strip q1 w hw
      obtain ⟨ef, -, ek, ev⟩ := spStrip_eq e
      have hbk0 : isBktFlag w0.flags := by rw [ef]; exact hbk
      refine ⟨fun ho => ?_, hvs l r' hr' (by rw [q6]; exact hl) w hw hbk⟩
      rw [hbm, ← ek] at ho
      rw [← ev]
      exact spBvalOK_mono _ _ _ _ ((n11 hl w0 hw0 hbk0).1 ho) hle
    · intro hl
      rw [q6] at hl
      obtain ⟨a1, a2, a3⟩ := n12 hl
      refine ⟨by rw [spLen_strip q1]; exact a1, by rw [spPgids_strip q1]; exact a2,
        fun w hw => ?_⟩
      obtain ⟨w0, hw0, e⟩ := spMem_strip q1 w hw
      obtain ⟨-, ep, -, -⟩ := spStrip_eq e
      rw [← ep]
      obtain ⟨b1, b2, b3⟩ := a3 w0 hw0
      refine ⟨by omega, fun l' hl' => ?_, fun hn => ?_⟩
      · rw [hnm] at hl'
        obtain ⟨r0, hr0, hp0⟩ := b2 l' hl'
        obtain ⟨r0', hr0', e0⟩ := hf l' r0 hr0
        exact ⟨r0', hr0', by rw [e0.2.2.2.2.2.2.2.2.2.1]; exact hp0⟩
      · rw [hnm] at hn
        exact spTreeWF_mono _ _ _ _ (b3 hn) hle
    · intro hp
      rw [q10] at hp ⊢
      obtain ⟨rp, hrp, hrl, hin, w, hw, hwp⟩ := n14 hp
      obtain ⟨rp', hrp', ep⟩ := hf _ rp hrp
      obtain ⟨w', hw', ew⟩ := spMem_strip (ws := rp'.ws) (ws' := rp.ws) ep.1.symm w hw
      exact ⟨rp', hrp', by rw [ep.2.2.2.2.2.1]; exact hrl, by rw [ep.2.1]; exact hin, w', hw',
        by rw [q9, (spStrip_eq ew).2.1]; exact hwp⟩
    · intro c hcin
      rw [q2] at hcin
      obtain ⟨rc, hrc, hpc⟩ := n16 c hcin
      obtain ⟨rc', hrc', ec⟩ := hf c rc hrc
      exact ⟨rc', hrc', by rw [ec.2.2.2.2.2.2.2.2.2.1]; exact hpc⟩
  · intro l1 i1 c1 l2 i2 c2 h1 h2 hne d hd
    rw [hpos] at h1 h2
    exact c9 l1 i1 c1 l2 i2 c2 h1 h2 hne d hd
  · intro l i c hp d hd
    rw [hpos] at hp
    rw [hnm]; exact c10 l i c hp d hd

theorem bktKeysB_ss {B B' : BRec} (h : spBSim B B') (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : bktKeysB W B bnd) : bktKeysB W B' bnd := by
  obtain ⟨hbv, hib, hnm, hbm, hipg, hf, hb⟩ := h
  obtain ⟨k1, k2, k3⟩ := hk
  refine ⟨by rw [hbv, hib]; exact k1, fun r' hr' => ?_, fun l r' hr' => ?_⟩
  · rw [hbv] at hr'
    obtain ⟨r, hr, e⟩ := hb _ r' hr'
    rw [e.2.2.2.2.2.2.2.2.2.1]; exact k2 r hr
  obtain ⟨r, hr, e⟩ := hb l r' hr'
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := e
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := k3 l r hr
  refine ⟨fun w hw => ?_, fun hp => by rw [q10] at hp; exact n2 hp, fun hp => ?_, fun hl => ?_,
    fun hl hu hp => ?_, fun hl w hw hbk hr0 ho => ?_⟩
  · obtain ⟨w0, hw0, ew⟩ := spMem_strip q1 w hw
    rw [← (spStrip_eq ew).2.2.1]; exact n1 w0 hw0
  · rw [q10] at hp ⊢
    obtain ⟨hkey, rp, i, w, hrp, hw, hwp, hwk, hbn⟩ := n3 hp
    obtain ⟨rp', hrp', ep⟩ := hf _ rp hrp
    obtain ⟨w', hw', ew⟩ := spGet_strip' ep.1 i w hw
    obtain ⟨-, ep2, ek, -⟩ := spStrip_eq ew
    exact ⟨fun h0 => hkey (q11.1 h0), rp', i, w', hrp', hw', by rw [← ep2, q9]; exact hwp,
      by rw [← ek, q4]; exact hwk, by rw [spEntryBnd_strip ep.1]; exact hbn⟩
  · rw [q6] at hl
    obtain ⟨a1, kind, a3⟩ := n4 hl
    refine ⟨by rw [spLen_strip q1]; exact a1, kind, fun i w hw => ?_⟩
    obtain ⟨w0, hw0, ew⟩ := spGet_strip q1 i w hw
    obtain ⟨-, ep, ek, -⟩ := spStrip_eq ew
    obtain ⟨b1, b2⟩ := a3 i w0 hw0
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rw [hnm, ← ep] at hl'
      obtain ⟨r0, hr0, hk0⟩ := b1 l' hl'
      obtain ⟨r0', hr0', e0⟩ := hf l' r0 hr0
      exact ⟨r0', hr0', by rw [e0.2.2.2.2.2.1]; exact hk0⟩
    · rw [hnm, ← ep] at hn
      rw [← ep, ← ek, spEntryBnd_strip q1]; exact b2 hn
  · rw [q6] at hl; rw [q8] at hu; rw [q10] at hp
    rw [spLen_strip q1]; exact n5 hl hu hp
  · rw [q6] at hl
    obtain ⟨w0, hw0, ew⟩ := spMem_strip q1 w hw
    obtain ⟨ef, -, ek, ev⟩ := spStrip_eq ew
    have ho' : ¬ opened B w0.key := by unfold opened at ho ⊢; rw [hbm] at ho; rw [ek]; exact ho
    rw [← ev]
    exact n6 hl w0 hw0 (by unfold isBktFlag at hbk ⊢; rw [ef]; exact hbk) (by rw [ev]; exact hr0) ho'

theorem rblKeysB_ss {B B' : BRec} (h : spBSim B B') (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : rblKeysB W B bnd none) : rblKeysB W B' bnd none := by
  obtain ⟨hbv, hib, hnm, hbm, hipg, hf, hb⟩ := h
  obtain ⟨k1, k2, k3⟩ := hk
  refine ⟨by rw [hbv, hib]; exact k1, fun r' hr' => ?_, fun l r' hr' => ?_⟩
  · rw [hbv] at hr'
    obtain ⟨r, hr, e⟩ := hb _ r' hr'
    rw [e.2.2.2.2.2.2.2.2.2.1]; exact k2 r hr
  obtain ⟨r, hr, e⟩ := hb l r' hr'
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := e
  obtain ⟨n1, n2, n3, n4, n5⟩ := k3 l r hr
  refine ⟨fun w hw => ?_, fun hp => ?_, fun hl => ?_, fun hd hl hu hp => ?_, fun hl w hw => ?_⟩
  · obtain ⟨w0, hw0, ew⟩ := spMem_strip q1 w hw
    rw [← (spStrip_eq ew).2.2.1]; exact n1 w0 hw0
  · rw [q10] at hp ⊢
    obtain ⟨hkey, rp, i, w, hrp, hw, hwp, hwk, hbn⟩ := n2 hp
    obtain ⟨rp', hrp', ep⟩ := hf _ rp hrp
    obtain ⟨w', hw', ew⟩ := spGet_strip' ep.1 i w hw
    obtain ⟨-, ep2, ek, -⟩ := spStrip_eq ew
    exact ⟨fun h0 => hkey (q11.1 h0), rp', i, w', hrp', hw', by rw [← ep2, q9]; exact hwp,
      by rw [← ek, q4]; exact hwk, by rw [spEntryBnd_strip ep.1]; exact hbn⟩
  · rw [q6] at hl
    obtain ⟨a1, a2, kind, a3⟩ := n3 hl
    refine ⟨fun hd => by rw [spLen_strip q1]; exact a1 hd, by rw [spWKey_strip q1]; exact a2,
      kind, fun i w hw => ?_⟩
    obtain ⟨w0, hw0, ew⟩ := spGet_strip q1 i w hw
    obtain ⟨-, ep, ek, -⟩ := spStrip_eq ew
    obtain ⟨b1, b2⟩ := a3 i w0 hw0
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rw [hnm, ← ep] at hl'
      obtain ⟨r0, hr0, hk0⟩ := b1 l' hl'
      obtain ⟨r0', hr0', e0⟩ := hf l' r0 hr0
      exact ⟨r0', hr0', by rw [e0.2.2.2.2.2.1]; exact hk0⟩
    · rw [hnm, ← ep] at hn
      rw [← ep, ← ek, spEntryBnd_strip q1]; exact b2 hn
  · rw [q6] at hl; rw [q8] at hu; rw [q10] at hp
    rw [spLen_strip q1]; exact n4 hd hl hu hp
  · rw [q6] at hl
    obtain ⟨w0, hw0, ew⟩ := spMem_strip q1 w hw
    obtain ⟨ef, ep, ek, ev⟩ := spStrip_eq ew
    obtain ⟨a1, a2⟩ := n5 hl w0 hw0
    refine ⟨by rw [← ep]; exact a1, fun hbk hr0 ho => ?_⟩
    have ho' : ¬ opened B w0.key := by unfold opened at ho ⊢; rw [hbm] at ho; rw [ek]; exact ho
    rw [← ev]
    exact a2 (by unfold isBktFlag at hbk ⊢; rw [ef]; exact hbk) (by rw [ev]; exact hr0) ho'

theorem entryIn_ss {B B' : BRec} (h : spBSim B B') (k v : List w8) (he : entryIn W B k v) :
    entryIn W B' k v := by
  have hpos := pagePosAt_ss h
  obtain ⟨hbv, hib, hnm, hbm, hipg, hf, hb⟩ := h
  rcases he with ⟨l, r, w, hr, hl, hw, hk, hbk, hv⟩ | ⟨c, p, pg, i, hc, ho, hpg, hlf, hi, hk, hfl, hv⟩
  · obtain ⟨r', hr', e⟩ := hf l r hr
    obtain ⟨w', hw', ew⟩ := spMem_strip (ws := r'.ws) (ws' := r.ws) e.1.symm w hw
    obtain ⟨ef, -, ek, ev⟩ := spStrip_eq ew
    exact Or.inl ⟨l, r', w', hr', by rw [e.2.2.2.2.2.1]; exact hl, hw', by rw [ek]; exact hk,
      by unfold isBktFlag at hbk ⊢; rw [ef]; exact hbk, by rw [ev]; exact hv⟩
  · refine Or.inr ⟨c, p, pg, i, ?_, ho, hpg, hlf, hi, hk, hfl, hv⟩
    unfold posRoot at hc ⊢
    rw [hbv, hib]
    rcases hc with h1 | ⟨l, j, hp, hlt⟩
    · exact Or.inl h1
    · exact Or.inr ⟨l, j, (hpos l j _).2 hp, hlt⟩

theorem bktRanked_ss {B B' : BRec} (h : spBSim B B') (hr : bktRanked B) : bktRanked B' := by
  obtain ⟨rk, N, hrk⟩ := hr
  refine ⟨rk, N, fun l r' hr' => ?_⟩
  obtain ⟨r, hr0, e⟩ := h.2.2.2.2.2.2 l r' hr'
  rw [e.2.2.2.2.2.2.2.2.2.1]; exact hrk l r hr0

theorem leafPg0_ss {B B' : BRec} (h : spBSim B B') (hl : leafPg0 B) : leafPg0 B' := by
  intro l r' hr' hlf w hw
  obtain ⟨r, hr, e⟩ := h.2.2.2.2.2.2 l r' hr'
  obtain ⟨w0, hw0, ew⟩ := spMem_strip e.1 w hw
  rw [← (spStrip_eq ew).2.1]
  exact hl l r hr (by rw [← e.2.2.2.2.2.1]; exact hlf) w0 hw0

theorem rblHt_ss {B B' : BRec} (h : spBSim B B') (ha : rblHt W B) : rblHt W B' := by
  obtain ⟨ht, pht, hp, hh⟩ := ha
  refine ⟨ht, pht, hp, fun l r' hr' => ?_⟩
  obtain ⟨r, hr, e⟩ := h.2.2.2.2.2.2 l r' hr'
  obtain ⟨h1, h2⟩ := hh l r hr
  refine ⟨fun hl => h1 (by rw [← e.2.2.2.2.2.1]; exact hl), fun hl w hw => ?_⟩
  obtain ⟨w0, hw0, ew⟩ := spMem_strip e.1 w hw
  obtain ⟨-, ep, -, -⟩ := spStrip_eq ew
  have := h2 (by rw [← e.2.2.2.2.2.1]; exact hl) w0 hw0
  rw [h.2.2.1, ← ep]; exact this

theorem bnd28_ss {B B' : BRec} (h : spBSim B B')
    (hb : ∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) :
    ∀ l r', B'.ns !! l = some r' → ∀ w ∈ r'.ws, w.key.length + w.value.length ≤ 2 ^ 28 := by
  intro l r' hr' w hw
  obtain ⟨r, hr, e⟩ := h.2.2.2.2.2.2 l r' hr'
  obtain ⟨w0, hw0, ew⟩ := spMem_strip e.1 w hw
  obtain ⟨-, -, ek, ev⟩ := spStrip_eq ew
  rw [← ek, ← ev]; exact hb l r hr w0 hw0

end pure

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

open Classical in
theorem nodeToks_ss (γ : GName) (W : WView) (B B' : BRec) (r r' : NRec) (hbm : B'.bm = B.bm)
    (hnm : B'.nm = B.nm) (e : spREq r r') : nodeToks (GF := GF) γ W B r ⊢ nodeToks γ W B' r' := by
  have hop : opened B' = opened B := by unfold opened; rw [hbm]
  unfold nodeToks
  rw [e.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.1, hop, hnm]
  iintro ⟨Hp, Hl⟩
  iframe Hp
  let g : w32 × w64 × List w8 × List w8 → IProp GF := fun x =>
    if r.nv.isLeaf' = true then
      (if isBktFlag x.1 ∧ inBucketRoot x.2.2.2 ≠ 0 ∧ ¬ opened B x.2.2.1 then
        pgToks γ (treePages W.pages (inBucketRoot x.2.2.2)) else emp)
    else (if B.nm !! x.2.1 = none then pgToks γ (xPages W.pages (opened B) (uint.nat x.2.1)) else emp)
  have e1 := BigSepL.bigSepL_map (PROP := IProp GF) (Φ := fun _ x => g x) (l := r.ws) spStrip
  have e2 := BigSepL.bigSepL_map (PROP := IProp GF) (Φ := fun _ x => g x) (l := r'.ws) spStrip
  rw [e.1] at e2
  have h1 : ([∗list] w ∈ r.ws, g (spStrip w)) =
      ([∗list] w ∈ r.ws, if r.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
          pgToks γ (treePages W.pages (inBucketRoot w.value)) else emp)
      else (if B.nm !! w.pgid = none then pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid))
        else emp)) := rfl
  have h2 : ([∗list] w ∈ r'.ws, g (spStrip w)) =
      ([∗list] w ∈ r'.ws, if r.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
          pgToks γ (treePages W.pages (inBucketRoot w.value)) else emp)
      else (if B.nm !! w.pgid = none then pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid))
        else emp)) := rfl
  rw [← h1, ← h2, ← e1, ← e2]
  iexact Hl

/-- The tokens of a bucket go to the same bucket up to sources. -/
theorem bktToks_ss (γ : GName) (W : WView) (B B' : BRec) (h : spBSim B B') :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W B' := by
  obtain ⟨hbv, hib, hnm, hbm, hipg, hf, hb⟩ := h
  unfold bktToks
  rw [hbv, hib]
  have hop : opened B' = opened B := by unfold opened; rw [hbm]
  split
  · rw [hop]
  · exact bigSepM_transfer _ _ B.ns B'.ns (fun k y hy => by
      obtain ⟨x, hx, e⟩ := hb k y hy
      exact ⟨x, hx, nodeToks_ss γ W B B' x y hbm hnm e⟩)

end toks

end bbolt
end EtcdGrove
end Perennial
