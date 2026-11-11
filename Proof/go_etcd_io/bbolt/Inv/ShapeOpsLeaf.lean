/-
**A leaf node's entries updated in place** (batch 37 item 14 and batch 38.5, S3):
`bktLocalOK_setLeaf` keeps a bucket searchable when one of its leaf nodes gets new entries whose
keys are among the old ones (sorted, live, bounded as `nodeClean`/`nodeKeys` ask), the node's
other fields unchanged; its corollary `bktLocalOK_putOpened` (U9's `Bucket.spill`, S3): the value
of an entry whose key is an opened bucket replaced by a persistent header (`node.put`'s post with
`wsPutAt` at a found key).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsBkt
public import Proof.go_etcd_io.bbolt.Write.NodeEnts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.Std go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section leaf
variable [GooseExts]

/-- The fields of a node record other than its entries (and inodes). -/
def sameShape (r r' : NRec) : Prop :=
  r'.nv.bucket' = r.nv.bucket' ∧ r'.nv.spilled' = r.nv.spilled' ∧ r'.nv.pgid' = r.nv.pgid' ∧
  r'.nv.key' = r.nv.key' ∧ r'.nv.isLeaf' = r.nv.isLeaf' ∧ r'.nv.parent' = r.nv.parent' ∧
  r'.nv.unbalanced' = r.nv.unbalanced' ∧ r'.cs = r.cs ∧ r'.key = r.key ∧ r'.ksrc = r.ksrc ∧
  r'.capOwn = r.capOwn

theorem sameShape_withEnts (r : NRec) (s : GoSlice) (ins : List Inode) (ws : List WEntry) :
    sameShape r (r.withEnts s ins ws) := by
  unfold sameShape NRec.withEnts; simp

/-- **A leaf's entries replaced keep its bucket searchable**: the new entries sorted, non-empty
keys among the old ones (so within the leaf's bounds), live, no child page, their nested buckets
as `nodeClean` and `nodeKeys` ask, non-empty if the leaf must be. -/
theorem bktLocalOK_setLeaf (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hb : bktLocalOK X bl) (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (hlf : r.nv.isLeaf' = true) (hsh : sameShape r r')
    (hins : r'.ins.length = r'.ws.length) (hsort : wsSorted r'.ws)
    (hkey : ∀ w ∈ r'.ws, 0 < w.key.length) (hlive : wsLive r'.ws)
    (hbkt : ∀ w ∈ r'.ws, isBktFlag w.flags →
      ((B.bm !! w.key).isSome = false → bvalOK X.v.pages X.t.mv.pgid'.toNat w.value) ∧
      (w.vs = Src.view ∨ w.vs = Src.own DFrac.discard))
    (hkeys : ∀ w ∈ r'.ws, ∃ w0 ∈ r.ws, w0.key = w.key)
    (hnest : ∀ w ∈ r'.ws, isBktFlag w.flags → inBucketRoot w.value ≠ 0 → ¬ opened B w.key →
      treeKeys X.v.pages (inBucketRoot w.value) none none)
    (hpg : ∀ w ∈ r'.ws, w.pgid = W64 0)
    (hne : r.nv.unbalanced' = false → r.nv.parent' ≠ null → 0 < r'.ws.length) :
    bktLocalOK (X.setNode bl l r') bl := by
  obtain ⟨hlb, B0, hB0, hc, ⟨bnd, hk⟩, hpl, hlv, hvw⟩ := hb
  rw [hB] at hB0; cases hB0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hsh
  unfold WX.setNode; rw [hB]
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
  -- nodeClean of every node
  have hclean : ∀ k rk, B'.ns !! k = some rk → nodeClean X.v X.t.mv.pgid'.toNat bl B' k rk := by
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
  refine ⟨hlb, B', GMap.lookup_insert _ _ _, ?_, ⟨bnd, ?_⟩, ?_, ?_, hvw⟩
  · -- bktClean
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, c9, c10, c11⟩ := hc
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
  · -- keys
    obtain ⟨k1, k2, k3⟩ := hk
    refine ⟨k1, fun rk h => ?_, fun k rk h => ?_⟩
    · rcases hcase _ rk h with ⟨e, rfl⟩ | ⟨-, h'⟩
      · rw [e6]; exact k2 r (e ▸ hr)
      · exact k2 rk h'
    · rcases hcase k rk h with ⟨rfl, rfl⟩ | ⟨hkl, h'⟩
      · obtain ⟨n1, n2, n3, -, n5, -⟩ := k3 k r hr
        refine ⟨fun w hw => ?_, fun h0 => n2 (e6 ▸ h0), fun h0 => ?_, fun h0 => ?_,
          fun _ hu hp => hne (e7 ▸ hu) (e6 ▸ hp), fun _ w hw hf => hnest w hw hf⟩
        · obtain ⟨w0, hw0, hk0⟩ := hkeys w hw
          rw [← hk0]; exact n1 w0 hw0
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
  · -- leaves' pages
    intro bl2 B2 h2 k rk h
    rw [GMap.lookup_singleton_iff] at h2
    split at h2
    · cases h2
      rcases hcase k rk h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
      · exact fun _ => hpg
      · exact hpl bl B (GMap.lookup_singleton_eq _ _) k rk h'
    · cases h2
  · -- live
    intro k rk h
    rcases hcase k rk h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
    · exact hlv k r hr
    · exact hlv k rk h'

theorem wKey_set_same (ws : List WEntry) (i : Nat) (e : WEntry) (he : e.key = wKey ws i)
    (hi : i < ws.length) (j : Nat) : wKey (ws.set i e) j = wKey ws j := by
  unfold wKey at he ⊢
  rw [List.getElem?_set]
  by_cases e' : i = j
  · subst e'; simp only [↓reduceIte, hi]; simpa using he
  · simp [e']

/-- **S3 (batch 38.5): a found entry of an opened bucket's key replaced by a persistent header**
(`Bucket.spill`'s root-bucket puts, U9: `node.put`'s post at a key of `B.bm`): the bucket stays
searchable. -/
theorem bktLocalOK_putOpened (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (s : GoSlice)
    (ins : List Inode) (k : List w8) (e : WEntry) (hb : bktLocalOK X bl)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hlf : r.nv.isLeaf' = true)
    (hf : wsFound r.ws k) (hek : e.key = k) (hop : opened B k)
    (hvs : e.vs = Src.view ∨ e.vs = Src.own DFrac.discard) (hks : e.ks ≠ Src.stale)
    (hpg : e.pgid = W64 0) (hins : ins.length = r.ws.length) :
    bktLocalOK (X.setNode bl l (r.withEnts s ins (wsPutAt r.ws k e))) bl := by
  have hb' := hb
  obtain ⟨-, B0, hB0, hc, ⟨bnd, hk⟩, hpl, -, -⟩ := hb'
  rw [hB] at hB0; cases hB0
  have hn := hc.2.2.2.2.2.2.2.1 l r hr
  obtain ⟨hi, hki⟩ := (Write.wsFound_iff r.ws k).1 hf
  have hws : wsPutAt r.ws k e = r.ws.set (wsIdx r.ws k) e := by
    rw [Write.wsPutAt_eq, if_pos hf]
  have hmem : ∀ w ∈ wsPutAt r.ws k e, w = e ∨ w ∈ r.ws := by
    intro w hw; rw [hws] at hw
    rcases List.mem_or_eq_of_mem_set hw with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- the old entry at the index
  obtain ⟨w0, hw0, hw0k⟩ : ∃ w0 ∈ r.ws, w0.key = k := by
    refine ⟨r.ws[wsIdx r.ws k], List.getElem_mem hi, ?_⟩
    unfold wKey at hki; rw [List.getElem?_eq_getElem hi] at hki; simpa using hki
  have hopk : (B.bm !! k).isSome = true := hop
  refine bktLocalOK_setLeaf X bl l B r _ hb hB hr hlf (sameShape_withEnts r s ins _) ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  · show ins.length = (wsPutAt r.ws k e).length
    rw [hws, List.length_set]; exact hins
  · show wsSorted (wsPutAt r.ws k e)
    intro i j hij hj
    have hset := wKey_set_same r.ws (wsIdx r.ws k) e (by rw [hek, hki]) hi
    rw [hws] at hj ⊢; rw [hset, hset]
    exact hn.2.2.2.1 i j hij (by simpa using hj)
  · intro w hw
    rcases hmem w hw with rfl | h
    · rw [hek, ← hw0k]; exact hn.2.2.2.2.1 w0 hw0
    · exact hn.2.2.2.2.1 w h
  · intro w hw
    rcases hmem w hw with rfl | h
    · refine ⟨hks, ?_⟩; rcases hvs with h | h <;> rw [h] <;> simp
    · exact hn.2.2.2.2.2.1 w h
  · intro w hw hfl
    rcases hmem w hw with rfl | h
    · refine ⟨fun h' => ?_, hvs⟩
      rw [hek, hopk] at h'; cases h'
    · exact hn.2.2.2.2.2.2.2.2.2.2.2.1 hlf w h hfl
  · intro w hw
    rcases hmem w hw with rfl | h
    · exact ⟨w0, hw0, hw0k.trans hek.symm⟩
    · exact ⟨w, h, rfl⟩
  · intro w hw hfl hR hno
    rcases hmem w hw with rfl | h
    · exact absurd (hek ▸ hop) hno
    · exact (hk.2.2 l r hr).2.2.2.2.2 hlf w h hfl hR hno
  · intro w hw
    rcases hmem w hw with rfl | h
    · exact hpg
    · exact hpl bl B (GMap.lookup_singleton_eq _ _) l r hr hlf w h
  · intro hu hp
    show 0 < (wsPutAt r.ws k e).length
    rw [hws, List.length_set]; exact (hk.2.2 l r hr).2.2.2.2.1 hlf hu hp

end leaf

end bbolt
end EtcdGrove
end Perennial
