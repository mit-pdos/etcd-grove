/-
`Bucket.spill`'s buckets: a clean bucket's nodes are its root's tree (`spTreeOK_of_clean`), so a
remap dereferences them all (`spDeref_sim`); the buckets the spill takes (`bucketUX`: `bucketU`,
or a degenerate inline one, `spDeg`) stay so, their nested buckets' values made persistent
(`bucketUX_deref`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Proof.go_etcd_io.bbolt.SpillBucketSim
public import Proof.go_etcd_io.bbolt.SpillBucketPersist
public import Proof.go_etcd_io.bbolt.SpillNodeForest
public import Proof.go_etcd_io.bbolt.SpillNodeStep
public import Proof.go_etcd_io.bbolt.SpillReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section tree
variable [ext : FfiSyntax]

theorem spDerefOK_of_clean (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (l : Loc) (r : NRec)
    (h : nodeClean W hwm bl B l r) : derefOK bl r := by
  obtain ⟨h1, h2, -, h4, h5, -, -, -, -, h10, -⟩ := h
  refine ⟨h1, h2, fun w hw => ⟨(h5 w hw).1, (h5 w hw).2, h4 w hw⟩, ?_⟩
  rcases h10 with h | ⟨hk, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨hs, Or.inr hk⟩

/-- A clean, ranked bucket with a root node (no parent): its nodes a tree from it
(`treeOK`). -/
theorem spTreeOK_of_clean (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (hr : bktRanked B) (hrn : B.bv.rootNode' ≠ null)
    (hp0 : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null) : treeOK bl B := by
  obtain ⟨rk, N, hrk⟩ := hr
  have hcl := hc.2.2.2.2.2.2.2.1
  have h5 := hc.2.2.2.2.1
  refine ⟨⟨rk, N, hrk, fun l r h => ?_, fun l r h hp => ?_, fun l r h => ?_⟩, ?_, ?_,
    fun l r h => spDerefOK_of_clean W hwm bl B l r (hcl l r h)⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15⟩ := hcl l r h
    exact h15
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := hcl l r h
    obtain ⟨rp, hrp, -, hin, -⟩ := h14 hp
    exact ⟨rp, hrp, hin⟩
  · obtain ⟨-, -, -, -, -, -, h7, -⟩ := hcl l r h
    exact (h5 _ _ h7).1
  · obtain ⟨-, r0, hr0, -⟩ := h5 _ _ (hc.2.2.2.1 hrn)
    exact ⟨r0, hr0, hp0 r0 hr0⟩
  · intro l r h hp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := hcl l r h
    exact (h13 hp).symm

/-- A node's record and its dereferenced one. -/
theorem spREq_deref (r r' : NRec) (h : derefNodeX r r') (hil : r.ins.length = r.ws.length)
    (hk : r.nv.key' = slice.nil ∨ 0 < r.key.length) : spREq r r' := by
  obtain ⟨⟨h1, h2, h3, h4, h5, -, h7⟩, h8⟩ := h
  refine ⟨?_, h3, ?_, h4, by rw [h1], by rw [h1], by rw [h1], by rw [h1], by rw [h1], by rw [h1], ?_⟩
  · rw [h2, List.map_map]; rfl
  · rw [h7, h2, List.length_map, hil]
  · constructor
    · intro e
      apply Classical.byContradiction
      intro hne
      rcases hk with hk | hk
      · exact hne hk
      · exact h8 hne hk e
    · exact h5

/-- A clean bucket whose nodes are its root's tree, dereferenced: the same bucket up to
sources, each node dereferenced or as it was. -/
theorem spDeref_sim (W : WView) (hwm : Nat) (bl : Loc) (B B' : BRec) (hc : bktClean W hwm bl B)
    (hr : bktRanked B) (hp0 : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null)
    (hd : derefStarX B B') :
    spBSim B B' ∧ ∀ l r', B'.ns !! l = some r' → ∃ r, B.ns !! l = some r ∧
      (derefNodeX r r' ∨ r' = r) := by
  rcases hd with rfl | hd
  · exact ⟨spBSim_refl _, fun l r' h => ⟨r', h, Or.inr rfl⟩⟩
  obtain ⟨e1, e2, e3, e4, e5, -, e7, e8, -⟩ := hd
  have hcl := hc.2.2.2.2.2.2.2.1
  have hreq : ∀ l r r', B.ns !! l = some r → derefNodeX r r' → spREq r r' := by
    intro l r r' hr' hdn
    obtain ⟨-, n2, -, -, -, -, -, -, -, n10, -⟩ := hcl l r hr'
    refine spREq_deref r r' hdn n2 ?_
    rcases n10 with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  by_cases hrn : B.bv.rootNode' = null
  · have hns := (hc.2.2.1 hrn).1
    have hns' : ∀ l r', B'.ns !! l = some r' → False := by
      intro l r' h
      obtain ⟨r, hr0, -⟩ := e7 l r' h
      rw [hns] at hr0; simp at hr0
    refine ⟨⟨e1, e2, e3, e4, e5, fun y ry h => ?_, fun y ry' h => (hns' y ry' h).elim⟩,
      fun l r' h => (hns' l r' h).elim⟩
    rw [hns] at h; simp at h
  have hT := spTreeOK_of_clean W hwm bl B hc hr hrn hp0
  obtain ⟨⟨rk, N, hTN⟩, ⟨r0, h0, hpn⟩, hroot, -⟩ := hT
  obtain ⟨S, hS, hm⟩ := kidsTree_rootN B.ns rk N hTN B.bv.rootNode' r0 h0 hroot
  have hlive := e8 hrn S [B.bv.rootNode'] B.bv.rootNode' (upPath.self _ r0 h0 hpn)
    (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) hS (fun l hl hlS => by
      rw [List.mem_singleton] at hl; subst hl
      exact absurd ((hm _).2 (by rw [h0]; rfl)) hlS)
  have hall : ∀ l r r', B.ns !! l = some r → B'.ns !! l = some r' → derefNodeX r r' ∨ r' = r := by
    intro l r r' h1 h2
    rcases (hlive l (Or.inl ((hm l).2 (by rw [h1]; rfl)))).2 r r' h1 h2 with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨⟨e1, e2, e3, e4, e5, fun y ry h => ?_, fun y ry' h => ?_⟩, fun l r' h => ?_⟩
  · obtain ⟨ry', hy'⟩ := Option.isSome_iff_exists.1 (hlive y (Or.inl ((hm y).2 (by rw [h]; rfl)))).1
    refine ⟨ry', hy', ?_⟩
    rcases hall y ry ry' h hy' with hd | rfl
    · exact hreq y ry ry' h hd
    · exact spREq_refl _
  · obtain ⟨ry, hy, -⟩ := e7 y ry' h
    refine ⟨ry, hy, ?_⟩
    rcases hall y ry ry' hy h with hd | rfl
    · exact hreq y ry ry' hy hd
    · exact spREq_refl _
  · obtain ⟨r, hr0, -⟩ := e7 l r' h
    exact ⟨r, hr0, hall l r r' hr0 h⟩

/-- `C` is the bucket `C0` up to sources, its nodes' sources live. -/
def spLive (C0 C : BRec) : Prop :=
  spBSim C0 C ∧ ∀ l r, C.ns !! l = some r → wsLive r.ws ∧ (r.nv.key' ≠ slice.nil → r.ksrc ≠ Src.stale)

theorem spLive_refl (W : WView) (hwm : Nat) (bl : Loc) (C : BRec) (hc : bktClean W hwm bl C) :
    spLive C C := by
  refine ⟨spBSim_refl C, fun l r h => ?_⟩
  obtain ⟨-, -, -, -, n5, -, -, -, -, n10, -⟩ := hc.2.2.2.2.2.2.2.1 l r h
  refine ⟨n5, fun hk => ?_⟩
  rcases n10 with e | ⟨-, e⟩
  · exact absurd e hk
  · exact e

theorem spLive_PB (C0 C : BRec) (h : spLive C0 C) : spLive C0 (spPB C) := by
  refine ⟨spBSim_trans h.1 (spBSim_PB C), fun l r h' => ?_⟩
  rw [spPB_lookup] at h'
  cases e : C.ns !! l with
  | none => rw [e] at h'; cases h'
  | some r0 =>
    rw [e] at h'; cases h'
    obtain ⟨a, b⟩ := h.2 l r0 e
    refine ⟨fun w hw => ?_, b⟩
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
    obtain ⟨c1, c2⟩ := a w0 hw0
    unfold spPW; split
    · exact ⟨c1, spPS_live _ c2⟩
    · exact ⟨c1, c2⟩

/-- The tree of a clean bucket, carried to the same bucket up to live sources. -/
theorem spTreeOK_live (W : WView) (hwm : Nat) (bl : Loc) (C0 C : BRec) (hc : bktClean W hwm bl C0)
    (hr : bktRanked C0) (hrn : C0.bv.rootNode' ≠ null)
    (hp0 : ∀ r, C0.ns !! C0.bv.rootNode' = some r → r.nv.parent' = null) (h : spLive C0 C) :
    treeOK bl C := by
  obtain ⟨⟨rk, N, hT1, hT2, hT3, hT4⟩, ⟨r0, h0, hpn⟩, hroot, hok⟩ :=
    spTreeOK_of_clean W hwm bl C0 hc hr hrn hp0
  obtain ⟨⟨hbv, hib, hnm, hbm, hipg, hf, hb⟩, hlive⟩ := h
  refine ⟨⟨rk, N, fun l r' h' => ?_, fun l r' h' => ?_, fun l r' h' hp => ?_, fun l r' h' => ?_⟩,
    ?_, fun l r' h' hp => ?_, fun l r' h' => ?_⟩
  · obtain ⟨r, hr0, e⟩ := hb l r' h'
    rw [e.2.2.2.2.2.2.2.2.2.1]; exact hT1 l r hr0
  · obtain ⟨r, hr0, e⟩ := hb l r' h'
    obtain ⟨a, b⟩ := hT2 l r hr0
    refine ⟨by rw [e.2.1]; exact a, fun c hc' => ?_⟩
    rw [e.2.1] at hc'
    obtain ⟨rc, hrc, hpc⟩ := b c hc'
    obtain ⟨rc', hrc', ec⟩ := hf c rc hrc
    exact ⟨rc', hrc', by rw [ec.2.2.2.2.2.2.2.2.2.1]; exact hpc⟩
  · obtain ⟨r, hr0, e⟩ := hb l r' h'
    rw [e.2.2.2.2.2.2.2.2.2.1] at hp ⊢
    obtain ⟨rp, hrp, hin⟩ := hT3 l r hr0 hp
    obtain ⟨rp', hrp', ep⟩ := hf _ rp hrp
    exact ⟨rp', hrp', by rw [ep.2.1]; exact hin⟩
  · obtain ⟨r, hr0, -⟩ := hb l r' h'
    exact hT4 l r hr0
  · rw [hbv]
    obtain ⟨r0', h0', e⟩ := hf _ r0 h0
    exact ⟨r0', h0', by rw [e.2.2.2.2.2.2.2.2.2.1]; exact hpn⟩
  · obtain ⟨r, hr0, e⟩ := hb l r' h'
    rw [hbv]; exact hroot l r hr0 (by rw [← e.2.2.2.2.2.2.2.2.2.1]; exact hp)
  · obtain ⟨r, hr0, e⟩ := hb l r' h'
    obtain ⟨d1, d2, d3, d4⟩ := hok l r hr0
    obtain ⟨l1, l2⟩ := hlive l r' h'
    refine ⟨by rw [e.2.2.2.2.1]; exact d1, by rw [e.2.2.1, spLen_strip e.1]; exact d2,
      fun w hw => ?_, ?_⟩
    · obtain ⟨w0, hw0, ew⟩ := spMem_strip e.1 w hw
      exact ⟨(l1 w hw).1, (l1 w hw).2, by rw [← (spStrip_eq ew).2.2.1]; exact (d3 w0 hw0).2.2⟩
    · by_cases hk : r'.nv.key' = slice.nil
      · exact Or.inl hk
      · right
        have hk0 : r.nv.key' ≠ slice.nil := fun h0 => hk (e.2.2.2.2.2.2.2.2.2.2.2 h0)
        rcases d4 with h4 | ⟨-, h4⟩
        · exact absurd h4 hk0
        · refine ⟨l2 hk, ?_⟩
          rw [e.2.2.2.2.2.2.2.2.1, e.2.2.2.1]; exact h4

/-- A dereference of a bucket whose nodes are a tree: the same bucket up to sources, each node
dereferenced or as it was. -/
theorem spDeref_simT (bl : Loc) (B B' : BRec) (hT : treeOK bl B)
    (hk : ∀ l r, B.ns !! l = some r → r.nv.key' = slice.nil ∨ 0 < r.key.length)
    (hd : derefStarX B B') :
    spBSim B B' ∧ ∀ l r', B'.ns !! l = some r' → ∃ r, B.ns !! l = some r ∧
      (derefNodeX r r' ∨ r' = r) := by
  rcases hd with rfl | hd
  · exact ⟨spBSim_refl _, fun l r' h => ⟨r', h, Or.inr rfl⟩⟩
  obtain ⟨e1, e2, e3, e4, e5, -, e7, e8, -⟩ := hd
  have hreq : ∀ l r r', B.ns !! l = some r → derefNodeX r r' → spREq r r' := by
    intro l r r' hr' hdn
    exact spREq_deref r r' hdn (hT.2.2.2 l r hr').2.1 (hk l r hr')
  obtain ⟨⟨rk, N, hTN⟩, ⟨r0, h0, hpn⟩, hroot, -⟩ := hT
  have hrn : B.bv.rootNode' ≠ null := hTN.2.2.2 _ r0 h0
  obtain ⟨S, hS, hm⟩ := kidsTree_rootN B.ns rk N hTN B.bv.rootNode' r0 h0 hroot
  have hlive := e8 hrn S [B.bv.rootNode'] B.bv.rootNode' (upPath.self _ r0 h0 hpn)
    (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) hS (fun l hl hlS => by
      rw [List.mem_singleton] at hl; subst hl
      exact absurd ((hm _).2 (by rw [h0]; rfl)) hlS)
  have hall : ∀ l r r', B.ns !! l = some r → B'.ns !! l = some r' → derefNodeX r r' ∨ r' = r := by
    intro l r r' h1 h2
    rcases (hlive l (Or.inl ((hm l).2 (by rw [h1]; rfl)))).2 r r' h1 h2 with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨⟨e1, e2, e3, e4, e5, fun y ry h => ?_, fun y ry' h => ?_⟩, fun l r' h => ?_⟩
  · obtain ⟨ry', hy'⟩ := Option.isSome_iff_exists.1 (hlive y (Or.inl ((hm y).2 (by rw [h]; rfl)))).1
    refine ⟨ry', hy', ?_⟩
    rcases hall y ry ry' h hy' with hd | rfl
    · exact hreq y ry ry' h hd
    · exact spREq_refl _
  · obtain ⟨ry, hy, -⟩ := e7 y ry' h
    refine ⟨ry, hy, ?_⟩
    rcases hall y ry ry' hy h with hd | rfl
    · exact hreq y ry ry' hy hd
    · exact spREq_refl _
  · obtain ⟨r, hr0, -⟩ := e7 l r' h
    exact ⟨r, hr0, hall l r r' hr0 h⟩

/-- A dereference keeps a bucket of the spill up to live sources (its original clean, ranked). -/
theorem spLive_deref (W : WView) (hwm : Nat) (bl : Loc) (C0 C C' : BRec) (hc : bktClean W hwm bl C0)
    (hr : bktRanked C0) (hp0 : ∀ r, C0.ns !! C0.bv.rootNode' = some r → r.nv.parent' = null)
    (h : spLive C0 C) (hd : derefStarX C C') : spLive C0 C' := by
  by_cases hrn : C0.bv.rootNode' = null
  · have hns := (hc.2.2.1 hrn).1
    have hC : C.ns = ∅ := by
      apply GMap.ext; intro l
      cases e : C.ns !! l with
      | none => show none = (∅ : GMap Loc NRec) !! l; simp
      | some r => obtain ⟨r0, hr0, -⟩ := h.1.2.2.2.2.2.2 l r e; rw [hns] at hr0; simp at hr0
    have hC' : ∀ l r', C'.ns !! l = some r' → False := by
      intro l r' e
      rcases hd with rfl | hd
      · rw [hC] at e; simp at e
      · obtain ⟨r, hr0, -⟩ := hd.2.2.2.2.2.2.1 l r' e
        rw [hC] at hr0; simp at hr0
    have hbm := derefStarX_bm C C' hd
    have hib : C'.ib = C.ib := by rcases hd with rfl | hd; rfl; exact hd.2.1
    have hnm : C'.nm = C.nm := by rcases hd with rfl | hd; rfl; exact hd.2.2.1
    have hipg : C'.ipg = C.ipg := by rcases hd with rfl | hd; rfl; exact hd.2.2.2.2.1
    obtain ⟨⟨a1, a2, a3, a4, a5, -, -⟩, -⟩ := h
    exact ⟨⟨hbm.2.trans a1, hib.trans a2, hnm.trans a3, hbm.1.trans a4, hipg.trans a5,
      fun y ry hy => by rw [hns] at hy; simp at hy, fun y ry h => (hC' y ry h).elim⟩,
      fun l r h => (hC' l r h).elim⟩
  have hT := spTreeOK_live W hwm bl C0 C hc hr hrn hp0 h
  have hk : ∀ l r, C.ns !! l = some r → r.nv.key' = slice.nil ∨ 0 < r.key.length := by
    intro l r hl
    obtain ⟨r0, hr0, e⟩ := h.1.2.2.2.2.2.2 l r hl
    obtain ⟨-, -, -, -, -, -, -, -, -, n10, -⟩ := hc.2.2.2.2.2.2.2.1 l r0 hr0
    rcases n10 with n | ⟨n, -⟩
    · exact Or.inl (e.2.2.2.2.2.2.2.2.2.2.2 n)
    · exact Or.inr (by rw [e.2.2.2.1]; exact n)
  obtain ⟨hsim, hsrc⟩ := spDeref_simT bl C C' hT hk hd
  refine ⟨spBSim_trans h.1 hsim, fun l r' h' => ?_⟩
  obtain ⟨r, hr0, hdr⟩ := hsrc l r' h'
  rcases hdr with hdr | rfl
  · refine ⟨fun w hw => ?_, fun _ => by rw [hdr.1.2.2.2.2.2.1]; nofun⟩
    rw [hdr.1.2.1] at hw
    obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
    exact ⟨by nofun, by nofun⟩
  · exact h.2 l r' hr0

end tree

section pre
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [float_sem : go.FloatConvSemantics]

/-- An inline bucket not materialized: no opened bucket, no node (after a remap, its inline page,
which the spill does not read, may be stale). -/
def spDeg (C : BRec) : Prop :=
  C.bv.rootNode' = null ∧ C.ib.root' = W64 0 ∧ C.bm = ∅ ∧ C.ns = ∅

/-- A bucket the spill takes (`bucketU`), or a degenerate one (`spDeg`). -/
def bucketUX (W : WView) (T : WTx) (K : Loc → Bool) (c : Loc) (C : BRec) : Prop :=
  bucketU W T K c C ∨ spDeg C

/-- The nested buckets of a bucket up to sources, its children as they were (`ib`, root node). -/
theorem bktNested_ss (W : WView) (T T' : WTx) (B B' : BRec) (h : spBSim B B') (hn : bktNested W T B)
    (hk : ∀ k c C, B.bm !! k = some c → T.bs !! c = some C →
      ∃ C', T'.bs !! c = some C' ∧ C'.ib = C.ib ∧ C'.bv.rootNode' = C.bv.rootNode') :
    bktNested W T' B' := by
  intro k c hc
  have hbm := h.2.2.2.1
  rw [hbm] at hc
  obtain ⟨C, v, hC, he, h16, hinl, hroot, hib⟩ := hn k c hc
  obtain ⟨C', hC', e1, e2⟩ := hk k c C hc hC
  exact ⟨C', v, hC', entryIn_ss W h k v he, h16, hinl, by rw [e1]; exact hroot,
    fun hn0 => by rw [e1]; exact hib (by rw [← e2]; exact hn0)⟩

/-- An unmaterialized inline bucket with its nested buckets' entries: none. -/
theorem spBm_empty (W : WView) (hwm : Nat) (T : WTx) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hn : bktNested W T B) (hrn : B.bv.rootNode' = null) (hr0 : B.ib.root' = W64 0) : B.bm = ∅ := by
  have hns := (hc.2.2.1 hrn).1
  apply GMap.ext; intro k
  cases e : B.bm !! k with
  | none => show none = (∅ : GMap GoString Loc) !! k; simp
  | some c =>
    exfalso
    obtain ⟨-, v, -, he, -⟩ := hn k c e
    rcases he with ⟨l, r, -, hr, -⟩ | ⟨cp, -, -, -, hpos, -⟩
    · rw [hns] at hr; simp at hr
    · rcases hpos with ⟨-, h0, -⟩ | ⟨l, i, ⟨r, -, hr, -⟩, -⟩
      · exact h0 hr0
      · rw [hns] at hr; simp at hr

/-- A bucket the spill takes, dereferenced (`derefStarX`) and its nested buckets' values made
persistent (`spPB`): still one. -/
theorem bucketUX_deref (W : WView) (T T' : WTx) (K K' : Loc → Bool) (d : Loc) (D D' : BRec)
    (hU : bucketUX W T K d D) (hd : derefStarX D D')
    (hwm : uint.nat T.mv.pgid' ≤ uint.nat T'.mv.pgid')
    (hK : ∀ l, (D.ns !! l).isSome → K' l = K l)
    (hkids : ∀ k c C, D.bm !! k = some c → T.bs !! c = some C →
      ∃ C', T'.bs !! c = some C' ∧ C'.ib = C.ib ∧ C'.bv.rootNode' = C.bv.rootNode') :
    bucketUX W T' K' d (spPB D') := by
  have hbm' := (derefStarX_bm D D' hd)
  have hns_sub : ∀ l r', D'.ns !! l = some r' → ∃ r, D.ns !! l = some r := by
    intro l r' h
    rcases hd with rfl | hd
    · exact ⟨r', h⟩
    · obtain ⟨r, hr, -⟩ := hd.2.2.2.2.2.2.1 l r' h
      exact ⟨r, hr⟩
  have hdeg_of : spDeg D → spDeg (spPB D') := by
    rintro ⟨h1, h2, h3, h4⟩
    have hib : D'.ib = D.ib := by
      rcases hd with rfl | hd
      · rfl
      · exact hd.2.1
    refine ⟨by show D'.bv.rootNode' = null; rw [hbm'.2]; exact h1,
      by show D'.ib.root' = W64 0; rw [hib]; exact h2,
      by show D'.bm = ∅; rw [hbm'.1]; exact h3, ?_⟩
    apply GMap.ext; intro l
    rw [spPB_lookup]
    cases e : D'.ns !! l with
    | none => show none = (∅ : GMap Loc NRec) !! l; simp
    | some r' =>
      obtain ⟨r, hr⟩ := hns_sub l r' e
      rw [h4] at hr; simp at hr
  rcases hU.symm with hdeg | hU
  · exact Or.inr (hdeg_of hdeg)
  obtain ⟨hc, ⟨bnd, hrbl⟩, hn, hr, hl, hht, hns, hthr⟩ := hU
  by_cases hi : D.bv.rootNode' = null ∧ D.ib.root' = W64 0
  · right
    apply hdeg_of
    exact ⟨hi.1, hi.2, spBm_empty W _ T d D hc hn hi.1 hi.2, (hc.2.2.1 hi.1).1⟩
  left
  have hp0 := hrbl.2.1
  obtain ⟨hsim, hsrc⟩ := spDeref_sim W _ d D D' hc hr hp0 hd
  have hsim2 := spBSim_trans hsim (spBSim_PB D')
  have hcl := hc.2.2.2.2.2.2.2.1
  have hsrc2 : ∀ l r'', (spPB D').ns !! l = some r'' → ∃ r r', D.ns !! l = some r ∧
      D'.ns !! l = some r' ∧ r'' = spPR r' ∧ (derefNodeX r r' ∨ r' = r) := by
    intro l r'' h
    rw [spPB_lookup] at h
    cases e : D'.ns !! l with
    | none => rw [e] at h; cases h
    | some r' =>
      rw [e] at h; cases h
      obtain ⟨r, hr0, hdr⟩ := hsrc l r' e
      exact ⟨r, r', hr0, rfl, rfl, hdr⟩
  refine ⟨bktClean_ss W _ d hsim2 hc _ hwm (fun h0 h1 => absurd ⟨h1, h0⟩ hi) ?_ ?_,
    ⟨bnd, rblKeysB_ss W hsim2 bnd hrbl⟩, bktNested_ss W T T' D _ hsim2 hn ?_,
    bktRanked_ss hsim2 hr, leafPg0_ss hsim2 hl, rblHt_ss W hsim2 hht, ?_, ?_⟩
  · intro l r'' h
    obtain ⟨r, r', hr0, hr', rfl, hdr⟩ := hsrc2 l r'' h
    obtain ⟨-, -, -, -, n5, -, -, -, -, n10, -⟩ := hcl l r hr0
    refine ⟨fun w hw => ?_, fun hk => ?_⟩
    · obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      rcases hdr with hdr | rfl
      · rw [hdr.1.2.1] at hw0
        obtain ⟨w1, -, rfl⟩ := List.mem_map.1 hw0
        unfold spPW ownFresh; split <;> simp [spPS]
      · obtain ⟨a, b⟩ := n5 w0 hw0
        unfold spPW; split
        · exact ⟨a, spPS_live _ b⟩
        · exact ⟨a, b⟩
    · show r'.ksrc ≠ Src.stale
      rcases hdr with hdr | rfl
      · rw [hdr.1.2.2.2.2.2.1]; nofun
      · rcases n10 with h | ⟨-, h⟩
        · exact absurd h hk
        · exact h
  · intro l r'' h hlf w hw hb
    obtain ⟨r, r', hr0, hr', rfl, hdr⟩ := hsrc2 l r'' h
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
    have hb0 : isBktFlag w0.flags := by
      unfold spPW at hb; split at hb <;> exact hb
    rcases hdr with hdr | rfl
    · rw [hdr.1.2.1] at hw0
      obtain ⟨w1, -, rfl⟩ := List.mem_map.1 hw0
      right
      exact spPW_vs _ hb0 (by nofun) (by nofun)
    · have hleaf : r'.nv.isLeaf' = true := hlf
      obtain ⟨-, -, -, -, -, -, -, -, -, -, n11, -⟩ := hcl l r' hr0
      rcases (n11 hleaf w0 hw0 hb0).2 with e | e
      · left; unfold spPW; rw [if_pos hb0, e]; rfl
      · right; unfold spPW; rw [if_pos hb0, e]; rfl
  · intro k c C hk hC
    exact hkids k c C hk hC
  · intro l r'' h
    obtain ⟨r, hr0, e⟩ := hsim2.2.2.2.2.2.2 l r'' h
    obtain ⟨a, b, c, -⟩ := hns l r hr0
    refine ⟨by rw [e.2.2.2.2.2.2.2.1]; exact a, by rw [e.2.2.2.2.2.2.1]; exact b,
      by rw [hK l (by rw [hr0]; rfl)]; exact c, ?_⟩
    exact bnd28_ss hsim2 (fun l r h => (hns l r h).2.2.2) l r'' h
  · show uint.Z (splitThr (W64 (W.ps : Int)) D'.bv.FillPercent') ≤ W.ps
    rw [hbm'.2]; exact hthr


/-- A bucket the spill takes (its original `D0`), up to live sources (`D`) and its nested buckets'
values made persistent (`spPB`): still one. -/
theorem bucketUX_live (W : WView) (T T' : WTx) (K K' : Loc → Bool) (d : Loc) (D0 D : BRec)
    (hU : bucketUX W T K d D0) (hl : spLive D0 D)
    (hwm : uint.nat T.mv.pgid' ≤ uint.nat T'.mv.pgid')
    (hK : ∀ l, (D0.ns !! l).isSome → K' l = K l)
    (hkids : ∀ k c C, D0.bm !! k = some c → T.bs !! c = some C →
      ∃ C', T'.bs !! c = some C' ∧ C'.ib = C.ib ∧ C'.bv.rootNode' = C.bv.rootNode') :
    bucketUX W T' K' d (spPB D) := by
  have hsim2 := spBSim_trans hl.1 (spBSim_PB D)
  obtain ⟨hbv, hib, hnm, hbm, hipg, hf, hb⟩ := hsim2
  have hdeg_of : spDeg D0 → spDeg (spPB D) := by
    rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by rw [hbv]; exact h1, by rw [hib]; exact h2, by rw [hbm]; exact h3, ?_⟩
    apply GMap.ext; intro l
    cases e : (spPB D).ns !! l with
    | none => show none = (∅ : GMap Loc NRec) !! l; simp
    | some r' =>
      obtain ⟨r, hr, -⟩ := hb l r' e
      rw [h4] at hr; simp at hr
  rcases hU.symm with hdeg | hU
  · exact Or.inr (hdeg_of hdeg)
  obtain ⟨hc, ⟨bnd, hrbl⟩, hn, hr, hll, hht, hns, hthr⟩ := hU
  by_cases hi : D0.bv.rootNode' = null ∧ D0.ib.root' = W64 0
  · right
    apply hdeg_of
    exact ⟨hi.1, hi.2, spBm_empty W _ T d D0 hc hn hi.1 hi.2, (hc.2.2.1 hi.1).1⟩
  left
  have hsim := spBSim_trans hl.1 (spBSim_PB D)
  refine ⟨bktClean_ss W _ d hsim hc _ hwm (fun h0 h1 => absurd ⟨h1, h0⟩ hi) ?_ ?_,
    ⟨bnd, rblKeysB_ss W hsim bnd hrbl⟩, bktNested_ss W T T' D0 _ hsim hn hkids,
    bktRanked_ss hsim hr, leafPg0_ss hsim hll, rblHt_ss W hsim hht, ?_, ?_⟩
  · intro l r'' h
    rw [spPB_lookup] at h
    cases e : D.ns !! l with
    | none => rw [e] at h; cases h
    | some r' =>
      rw [e] at h; cases h
      exact (spLive_PB D0 D hl).2 l (spPR r') (by rw [spPB_lookup, e]; rfl)
  · intro l r'' h hlf w hw hbk
    rw [spPB_lookup] at h
    cases e : D.ns !! l with
    | none => rw [e] at h; cases h
    | some r' =>
      rw [e] at h; cases h
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      have hb0 : isBktFlag w0.flags := by
        unfold spPW at hbk; split at hbk <;> exact hbk
      have hs := ((hl.2 l r' e).1 w0 hw0).2
      unfold spPW; rw [if_pos hb0]
      show spPS w0.vs = Src.view ∨ spPS w0.vs = Src.own DFrac.discard
      cases e2 : w0.vs with
      | own _ => right; rfl
      | view => left; rfl
      | stale => exact absurd e2 hs
  · intro l r'' h
    obtain ⟨r, hr0, e⟩ := hb l r'' h
    obtain ⟨a, b, c, -⟩ := hns l r hr0
    refine ⟨by rw [e.2.2.2.2.2.2.2.1]; exact a, by rw [e.2.2.2.2.2.2.1]; exact b,
      by rw [hK l (by rw [hr0]; rfl)]; exact c, ?_⟩
    exact bnd28_ss hsim (fun l r h => (hns l r h).2.2.2) l r'' h
  · show uint.Z (splitThr (W64 (W.ps : Int)) (spPB D).bv.FillPercent') ≤ W.ps
    rw [hbv]; exact hthr

/-- The nested buckets of `B` over a transaction whose children of `B` are the same. -/
theorem bktNested_T (W : WView) (T T' : WTx) (B : BRec) (hn : bktNested W T B)
    (hk : ∀ k c C, B.bm !! k = some c → T.bs !! c = some C → T'.bs !! c = some C) :
    bktNested W T' B := by
  intro k c hc
  obtain ⟨C, v, hC, rest⟩ := hn k c hc
  exact ⟨C, v, hk k c C hc hC, rest⟩

/-- A bucket the spill takes, over a transaction with the same children and a higher high-water
mark. -/
theorem bucketUX_T (W : WView) (T T' : WTx) (K : Loc → Bool) (d : Loc) (D : BRec)
    (hU : bucketUX W T K d D) (hwm : uint.nat T.mv.pgid' ≤ uint.nat T'.mv.pgid')
    (hk : ∀ k c C, D.bm !! k = some c → T.bs !! c = some C → T'.bs !! c = some C) :
    bucketUX W T' K d D := by
  rcases hU with ⟨hc, hrb, hn, hr, hl, hht, hns, hthr⟩ | hdeg
  · refine Or.inl ⟨bktClean_ss W _ d (spBSim_refl D) hc _ hwm ?_ ?_ ?_, hrb, bktNested_T W T T' D hn hk,
      hr, hl, hht, hns, hthr⟩
    · intro h0 h1
      exact (hc.1 h0 h1).2.1
    · intro l r h
      obtain ⟨-, -, -, -, n5, -, -, -, -, n10, -⟩ := hc.2.2.2.2.2.2.2.1 l r h
      refine ⟨n5, fun hk' => ?_⟩
      rcases n10 with e | ⟨-, e⟩
      · exact absurd e hk'
      · exact e
    · intro l r h hl w hw hb
      obtain ⟨-, -, -, -, -, -, -, -, -, -, n11, -⟩ := hc.2.2.2.2.2.2.2.1 l r h
      exact (n11 hl w hw hb).2
  · exact Or.inr hdeg


/-- A bucket reached from another opened bucket of `bl` is not the opened bucket `cv0`. -/
theorem spSib_ne (T : WTx) (dep : Loc → Nat)
    (hdep : ∀ b C name c, T.bs !! b = some C → C.bm !! name = some c → dep c < dep b)
    (hbu : bmUnique T) (bl : Loc) (B : BRec) (hB : T.bs !! bl = some B) (key k : GoString)
    (cv0 c d : Loc) (h1 : B.bm !! key = some cv0) (h2 : B.bm !! k = some c) (hk : k ≠ key)
    (hr : bktReach T c d) : d ≠ cv0 := by
  intro e
  subst e
  cases hr with
  | root => exact hk (hbu bl B k bl B key c hB h2 hB h1).2
  | child p P name _ hp hP hn =>
    obtain ⟨e, -⟩ := hbu p P name bl B key _ hP hn hB h1
    rw [e] at hp
    have h3 := hdep bl B k c hB h2
    have h4 := rs_dep T dep hdep c bl hp
    omega

/-- The inlineable child after its free: an inline bucket (root 0), its root node without a
page. -/
def spInlC (C : BRec) (r0 : NRec) : BRec :=
  { C with ib := ({ C.ib with root' := W64 0 } : internal.common.InBucket),
           ns := <[C.bv.rootNode' := ({ r0 with nv := ({ r0.nv with pgid' := W64 0 } : node) } : NRec)]> C.ns }

end pre

section g
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- Only the bucket `b`'s root (`ib`) changed: the spill's facts kept. -/
theorem spillG_setIb (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (b : Loc) (B : BRec) (x : internal.common.InBucket)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hB : T.bs !! b = some B) :
    spillG (hG := hG) W txl txid (setB T b { B with ib := x }) ρ F := by
  exact spillG_setB W txl txid T ρ F b B _ hg hB rfl rfl
    (hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 b B hB).1

/-- The inlineable child freed (its root's page pending, or none), its record `spInlC`: the
spill's facts kept. -/
theorem spillG_inl (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ ρ' : DBState)
    (F F' : GMap Nat (List w8)) (cv0 : Loc) (C : BRec) (r0 : NRec)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hC : T.bs !! cv0 = some C)
    (hr0 : C.ns !! C.bv.rootNode' = some r0) (hok : ∃ v0 v1, dbOK ρ v0 v1)
    (hρ : (ρ' = ρ ∧ F' = F) ∨ (∃ id k, ρ' = { ρ with fl := ρ.fl.freePages txid id k } ∧
      freedOK W ρ'.fl txid F')) :
    spillG (hG := hG) W txl txid (setB T cv0 (spInlC C r0)) ρ' F' := by
  have hg' : spillG (hG := hG) W txl txid T ρ' F' := by
    rcases hρ with ⟨rfl, rfl⟩ | ⟨id, k, rfl, hf⟩
    · exact hg
    · exact spSpillG_free W txl txid T ρ F F' id k hg hok hf
  have h1 := spSpillG_setN W txl txid T ρ' F' cv0 C C.bv.rootNode' r0
    ({ r0 with nv := { r0.nv with pgid' := W64 0 } } : NRec) hg' hC hr0 rfl rfl id
    (fun ⟨a, b, c, d⟩ => ⟨a, b, c, by
      rcases d with d | ⟨d1, -⟩
      · exact Or.inl d
      · exact Or.inr ⟨d1, Or.inl rfl⟩⟩)
  have h2 := spillG_setIb W txl txid _ ρ' F' cv0 _ ({ C.ib with root' := W64 0 } : internal.common.InBucket)
    h1 (GMap.lookup_insert _ _ _)
  have e : setB (setB T cv0 (setN C C.bv.rootNode' ({ r0 with nv := { r0.nv with pgid' := W64 0 } } : NRec)))
      cv0 { setN C C.bv.rootNode' ({ r0 with nv := { r0.nv with pgid' := W64 0 } } : NRec) with
        ib := ({ C.ib with root' := W64 0 } : internal.common.InBucket) } =
      setB T cv0 (spInlC C r0) := by
    unfold setB
    rw [GMap.insert_insert]
    rfl
  rw [← e]; exact h2

theorem kidRes_bufs (γ : GName) (W : WView) (T T' : WTx) (B : BRec) (k : List w8)
    (h : T'.bufs = T.bufs) (hm : T'.mv = T.mv) : kidRes (GF := GF) γ W T' B k = kidRes γ W T B k := by
  unfold kidRes spillPages; rw [h, hm]

theorem kidsRes_bufs (γ : GName) (W : WView) (T T' : WTx) (B : BRec) (ks : List GoString)
    (h : T'.bufs = T.bufs) (hm : T'.mv = T.mv) :
    ([∗list] k ∈ ks, kidRes (GF := GF) γ W T' B k) = [∗list] k ∈ ks, kidRes γ W T B k := by
  simp only [kidRes_bufs γ W T T' B _ h hm]

theorem spDerefOK_PR (bl : Loc) (r : NRec) (h : derefOK bl r) : derefOK bl (spPR r) := by
  obtain ⟨a, b, c, d⟩ := h
  refine ⟨a, by show r.ins.length = (r.ws.map spPW).length; rw [List.length_map]; exact b, ?_, d⟩
  intro w hw
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
  obtain ⟨c1, c2, c3⟩ := c w0 hw0
  unfold spPW; split
  · exact ⟨c1, spPS_live _ c2, c3⟩
  · exact ⟨c1, c2, c3⟩

theorem spNoView_PR (r : NRec) (h : noViewRec r) : noViewRec (spPR r) := by
  obtain ⟨a, b⟩ := h
  refine ⟨fun w hw => ?_, b⟩
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
  obtain ⟨c1, c2⟩ := a w0 hw0
  unfold spPW; split
  · refine ⟨c1, ?_⟩
    show spPS w0.vs ≠ Src.view
    cases e : w0.vs with
    | own _ => simp [spPS]
    | view => exact absurd e c2
    | stale => simp [spPS]
  · exact ⟨c1, c2⟩

/-- A bucket's nested buckets' values made persistent: the spill's facts kept. -/
theorem spillG_persist (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (bl : Loc) (B : BRec) (hg : spillG (hG := hG) W txl txid T ρ F)
    (hB : T.bs !! bl = some B) : spillG (hG := hG) W txl txid (setB T bl (spPB B)) ρ F := by
  have hag : ∀ l, nAgree B.ns (spPB B).ns l := by
    intro l rl hl
    exact ⟨spPR rl, by rw [spPB_lookup, hl]; rfl, rfl, rfl⟩
  apply spillG_setB W txl txid T ρ F bl B (spPB B) hg hB rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hr⟩ := hg
  rcases (hr.2.2.2 bl B hB).1 with h0 | ⟨S, ⟨p, top, hup, hnd, hkt, hpv⟩, hdok⟩
  · exact Or.inl h0
  · right
    refine ⟨S, ⟨p, top, upPath_mono _ _ hup (fun l _ => hag l), hnd,
      kidsTree_mono _ _ S.length top S (Nat.le_refl _) (fun l _ => hag l) hkt, fun l hl hlS => ?_⟩,
      fun l hl => ?_⟩
    · obtain ⟨rl, hrl, hnvl⟩ := hpv l hl hlS
      exact ⟨spPR rl, by rw [spPB_lookup, hrl]; rfl, spNoView_PR rl hnvl⟩
    · obtain ⟨rl, hrl, hdl⟩ := hdok l hl
      exact ⟨spPR rl, by rw [spPB_lookup, hrl]; rfl, spDerefOK_PR bl rl hdl⟩

/-- A bucket's nested buckets' values made persistent, in the spill state. -/
theorem spillR_persist (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (hB : T.bs !! bl = some B) :
    spillR I γd γ W txl txid T ρ F K ⊢ |==> spillR I γd γ W txl txid (setB T bl (spPB B)) ρ F K := by
  iintro Hs
  icases (spillR_bkt I γd γ W txl txid T ρ F K bl B hB) $$ Hs with ⟨Hb, Hc, Hback⟩
  ihave H := (bktOwnX_persist W bl B K) $$ [Hb Hc]
  · iframe
  imod H with ⟨Hb, Hc⟩
  imodintro
  iapply Hback $$ %(spPB B) %K [] Hb Hc
  ipureintro; intro l h; exact absurd rfl h

end g

end bbolt
end EtcdGrove
end Perennial
