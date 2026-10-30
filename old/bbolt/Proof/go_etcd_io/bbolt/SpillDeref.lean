/-
`Bucket.dereference` during the spill (`Bucket.dereference.xspec`): the lemmas of
`WriteDeref.lean` and `Bucket__dereference.lean` over `nodeOwnX` (`SpillOwn.lean`), each node
keeping its struct but its key (`derefNodeK`, `keepM`); the buckets dereferenced as
`derefBktX` says (`WriteDerefB.lean`'s composition, restated: `derefMX`, `child_preX`, ...).
-/
module

public import Proof.go_etcd_io.bbolt.SpillOwn
public import Proof.go_etcd_io.bbolt.WriteDeref
public import Proof.go_etcd_io.bbolt.WriteDerefB
public import Spec.go_etcd_io.bbolt.node__root
public import Spec.go_etcd_io.bbolt.node__dereference_w

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- `r'` is `r` dereferenced, its struct the same but its key. -/
def derefNodeK (r r' : NRec) : Prop := derefNodeX r r' ∧ r'.nv = { r.nv with key' := r'.nv.key' }

/-- `r'` is `r` dereferenced, or `r` itself keeping no byte of the view. -/
def dnX (r r' : NRec) : Prop := derefNodeX r r' ∨ (r' = r ∧ noViewRec r)

theorem derefNodeX_trans (r r' r'' : NRec) (h : derefNodeX r r') (h' : derefNodeX r' r'') :
    derefNodeX r r'' := by
  refine ⟨derefNode_trans _ _ _ h.1 h'.1, fun hk hl => ?_⟩
  have hkey : r'.key = r.key := h.1.2.2.2.1
  exact h'.2 (h.2 hk hl) (by rw [hkey]; exact hl)

theorem derefNode_noView (r r' : NRec) (h : derefNode r r') : noViewRec r' := by
  obtain ⟨-, h2, -, -, -, h6, -⟩ := h
  refine ⟨fun w hw => ?_, by rw [h6]; nofun⟩
  rw [h2] at hw
  obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
  exact ⟨by simp [ownFresh], by simp [ownFresh]⟩

theorem dnX_trans (r r' r'' : NRec) (h : dnX r r') (h' : dnX r' r'') : dnX r r'' := by
  rcases h with h | ⟨rfl, hv⟩
  · rcases h' with h' | ⟨rfl, -⟩
    · exact Or.inl (derefNodeX_trans _ _ _ h h')
    · exact Or.inl h
  · exact h'

theorem dnX_agree (r r' : NRec) (h : dnX r r') : r'.nv.parent' = r.nv.parent' ∧ r'.cs = r.cs := by
  rcases h with h | ⟨rfl, -⟩
  · exact ⟨(derefNode_agree r r' h.1).1, (derefNode_agree r r' h.1).2.1⟩
  · exact ⟨rfl, rfl⟩

theorem dnX_noView (r r' : NRec) (h : dnX r r') : noViewRec r' := by
  rcases h with h | ⟨rfl, hv⟩
  · exact derefNode_noView r r' h.1
  · exact hv

/-- A node dereferenced, kept (no byte of the view), or made stale (outside the live tree and the
root's chain). -/
def dnX3 (r r' : NRec) : Prop := derefNodeX r r' ∨ (r' = r ∧ noViewRec r) ∨ r' = staleRec r

theorem staleW_idem (w : WEntry) : staleW (staleW w) = staleW w := by
  simp only [staleW, staleOf_idem]

theorem staleRec_idem (r : NRec) : staleRec (staleRec r) = staleRec r := by
  have h : (staleW ∘ staleW) = staleW := funext staleW_idem
  simp only [staleRec, List.map_map, h, staleOf_idem]

theorem staleOf_of_ne (s : Src) (h : s ≠ Src.view) : staleOf s = s := by
  cases s <;> simp_all [staleOf]

theorem staleRec_of_noView (r : NRec) (h : noViewRec r) : staleRec r = r := by
  obtain ⟨hw, hk⟩ := h
  have hws : r.ws.map staleW = r.ws.map id := by
    apply List.map_congr_left
    intro w hw'
    obtain ⟨h1, h2⟩ := hw w hw'
    simp only [staleW, staleOf_of_ne _ h1, staleOf_of_ne _ h2, id]
  rw [List.map_id] at hws
  unfold staleRec
  rw [hws, staleOf_of_ne _ hk]

theorem derefNodeX_of_stale (r r' : NRec) (h : derefNodeX (staleRec r) r') : derefNodeX r r' := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hk⟩ := h
  refine ⟨⟨h1, ?_, h3, h4, h5, h6, h7⟩, hk⟩
  rw [h2]; show (r.ws.map staleW).map ownFresh = r.ws.map ownFresh
  rw [List.map_map]; rfl

theorem dnX3_of_dnX (r r' : NRec) (h : dnX r r') : dnX3 r r' := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem dnX3_trans (r r1 r2 : NRec) (h : dnX3 r r1) (h' : dnX3 r1 r2) : dnX3 r r2 := by
  rcases h with h | ⟨rfl, hv⟩ | rfl
  · rcases h' with h' | ⟨rfl, -⟩ | rfl
    · exact Or.inl (derefNodeX_trans _ _ _ h h')
    · exact Or.inl h
    · rw [staleRec_of_noView _ (derefNode_noView _ _ h.1)]; exact Or.inl h
  · exact h'
  · rcases h' with h' | ⟨rfl, -⟩ | rfl
    · exact Or.inl (derefNodeX_of_stale _ _ h')
    · exact Or.inr (Or.inr rfl)
    · rw [staleRec_idem]; exact Or.inr (Or.inr rfl)

theorem dnX3_agree (r r' : NRec) (h : dnX3 r r') : r'.nv.parent' = r.nv.parent' ∧ r'.cs = r.cs := by
  rcases h with h | h | rfl
  · exact dnX_agree r r' (Or.inl h)
  · exact dnX_agree r r' (Or.inr h)
  · exact ⟨rfl, rfl⟩

theorem dnX3_noView (r r' : NRec) (h : dnX3 r r') : noViewRec r' := by
  rcases h with h | h | rfl
  · exact dnX_noView r r' (Or.inl h)
  · exact dnX_noView r r' (Or.inr h)
  · exact staleRec_noView r

/-- The live nodes' structure (`liveNodesX`: path `p`, top `top`, tree `S`) of `B` holds in `B'`,
`B` dereferenced. -/
theorem liveX_transfer (B B' : BRec) (hbv : B'.bv = B.bv)
    (S p : List Loc) (top : Loc)
    (hkept : ∀ l, l ∈ S ∨ l ∈ p → (B'.ns !! l).isSome)
    (hns : ∀ l, l ∈ S ∨ l ∈ p → ∀ r r', B.ns !! l = some r → B'.ns !! l = some r' → dnX r r')
    (hu : upPath B.ns B.bv.rootNode' p top) (hk : kidsTree B.ns top S)
    (hq : ∀ l ∈ p, l ∉ S → ∃ r, B.ns !! l = some r ∧ noViewRec r) :
    upPath B'.ns B'.bv.rootNode' p top ∧ kidsTree B'.ns top S ∧
      ∀ l ∈ p, l ∉ S → ∃ r, B'.ns !! l = some r ∧ noViewRec r := by
  have hag : ∀ l, l ∈ S ∨ l ∈ p → nAgree B.ns B'.ns l := by
    intro l hl r hr
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (hkept l hl)
    have hd := hns l hl r r' hr hr'
    exact ⟨r', hr', (dnX_agree _ _ hd).2, (dnX_agree _ _ hd).1⟩
  refine ⟨?_, kidsTree_mono B.ns B'.ns S.length top S (Nat.le_refl _) (fun l hl => hag l (Or.inl hl)) hk,
    fun l hl hS => ?_⟩
  · rw [hbv]; exact upPath_mono B.ns B'.ns hu (fun x hx => hag x (Or.inr hx))
  · obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (hkept l (Or.inr hl))
    obtain ⟨r0, hr0, -⟩ := hq l hl hS
    exact ⟨r', hr', dnX_noView _ _ (hns l (Or.inr hl) r0 r' hr0 hr')⟩

theorem derefBktX_trans (B B' B'' : BRec) (h : derefBktX B B') (h' : derefBktX B' B'') :
    derefBktX B B'' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h'
  refine ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, ?_, ?_, ?_,
    fun l h => b9 l (a9 l h)⟩
  · rw [b6, a6, staleOf_idem]
  · intro l r'' hr''
    obtain ⟨r', hr', hd'⟩ := b7 l r'' hr''
    obtain ⟨r, hr, hd⟩ := a7 l r' hr'
    exact ⟨r, hr, dnX3_trans r r' r'' hd hd'⟩
  · intro hn S p top hu hnd hk hq l hl
    have hn' : B'.bv.rootNode' ≠ null := by rw [a1]; exact hn
    have h8 := a8 hn S p top hu hnd hk hq
    obtain ⟨hu', hk', hq'⟩ := liveX_transfer B B' a1 S p top (fun l hl => (h8 l hl).1)
      (fun l hl => (h8 l hl).2) hu hk hq
    obtain ⟨hs1, hd1⟩ := h8 l hl
    obtain ⟨hs2, hd2⟩ := b8 hn' S p top hu' hnd hk' hq' l hl
    refine ⟨hs2, fun r r'' hr hr'' => ?_⟩
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hs1
    exact dnX_trans r r' r'' (hd1 r r' hr hr') (hd2 r' r'' hr' hr'')

/-- The bucket `y` (record `Y`) is ready for `dereference` (`liveNodesX`). -/
def nodesReadyX (y : Loc) (Y : BRec) : Prop :=
  Y.bv.rootNode' = null ∨ ∃ S, liveNodesX Y S ∧ ∀ l ∈ S, ∃ r, Y.ns !! l = some r ∧ derefOK y r

theorem derefBktX_ready (y : Loc) (Y Y' : BRec) (h : nodesReadyX y Y) (hd : derefBktX Y Y') :
    nodesReadyX y Y' := by
  have hbv := hd.1
  rcases h with h | ⟨S, ⟨p, top, hu, hnd, hk, hq⟩, hok⟩
  · left; rw [hbv]; exact h
  · by_cases hn : Y.bv.rootNode' = null
    · left; rw [hbv]; exact hn
    right
    have h8 := hd.2.2.2.2.2.2.2.1 hn S p top hu hnd hk hq
    obtain ⟨hu', hk', hq'⟩ := liveX_transfer Y Y' hbv S p top (fun l hl => (h8 l hl).1)
      (fun l hl => (h8 l hl).2) hu hk hq
    refine ⟨S, ⟨p, top, hu', hnd, hk', hq'⟩, fun l hS => ?_⟩
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (h8 l (Or.inl hS)).1
    obtain ⟨r, hr, hok1⟩ := hok l hS
    have hdn := (h8 l (Or.inl hS)).2 r r' hr hr'
    refine ⟨r', hr', ?_⟩
    rcases hdn with hdn | ⟨rfl, -⟩
    · exact derefOK_derefNode y _ r' hok1 hdn.1
    · exact hok1

/-- `B'` is `B` or `B` dereferenced. -/
def derefStarX (B B' : BRec) : Prop := B' = B ∨ derefBktX B B'

theorem derefStarX_bm (B B' : BRec) (h : derefStarX B B') : B'.bm = B.bm ∧ B'.bv = B.bv := by
  rcases h with rfl | h
  · exact ⟨rfl, rfl⟩
  · exact ⟨h.2.2.2.1, h.1⟩

theorem derefStarX_trans (B B' B'' : BRec) (h : derefStarX B B') (h' : derefStarX B' B'') :
    derefStarX B B'' := by
  rcases h with rfl | h
  · exact h'
  rcases h' with rfl | h'
  · exact Or.inr h
  · exact Or.inr (derefBktX_trans B B' B'' h h')

theorem star_bktX (B B' B'' : BRec) (h : derefStarX B B') (h' : derefBktX B' B'') : derefBktX B B'' := by
  rcases h with rfl | h
  · exact h'
  · exact derefBktX_trans B B' B'' h h'

theorem bkt_starX (B B' B'' : BRec) (h : derefBktX B B') (h' : derefStarX B' B'') : derefBktX B B'' := by
  rcases h' with rfl | h'
  · exact h
  · exact derefBktX_trans B B' B'' h h'

theorem derefStarX_ready (y : Loc) (Y Y' : BRec) (h : nodesReadyX y Y) (hd : derefStarX Y Y') :
    nodesReadyX y Y' := by
  rcases hd with rfl | hd
  · exact h
  · exact derefBktX_ready y Y Y' h hd

/-- The buckets reachable from `x` are in `bs`, ready for `dereference`. -/
def readyAtX (bs : GMap Loc BRec) (x : Loc) : Prop :=
  ∀ y, reachB bs x y → ∃ Y, bs !! y = some Y ∧ nodesReadyX y Y

/-- Every bucket of `bs` is the same or dereferenced in `bs'`. -/
def derefMX (bs bs' : GMap Loc BRec) : Prop :=
  (∀ y, (bs !! y).isSome ↔ (bs' !! y).isSome) ∧
  ∀ y Y Y', bs !! y = some Y → bs' !! y = some Y' → derefStarX Y Y'

/-- The buckets reachable from `x` in `bs` are dereferenced in `bs'`. -/
def derefFromX (bs bs' : GMap Loc BRec) (x : Loc) : Prop :=
  ∀ y, reachB bs x y → ∃ Y Y', bs !! y = some Y ∧ bs' !! y = some Y' ∧ derefBktX Y Y'

theorem derefMX_refl (bs : GMap Loc BRec) : derefMX bs bs :=
  ⟨fun _ => Iff.rfl, fun y Y Y' h h' => by rw [h] at h'; cases h'; exact Or.inl rfl⟩

theorem derefMX_get (bs bs' : GMap Loc BRec) (h : derefMX bs bs') (y : Loc) (Y' : BRec)
    (hy : bs' !! y = some Y') : ∃ Y, bs !! y = some Y ∧ derefStarX Y Y' := by
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 ((h.1 y).2 (by rw [hy]; rfl))
  exact ⟨Y, hY, h.2 y Y Y' hY hy⟩

theorem derefMX_get' (bs bs' : GMap Loc BRec) (h : derefMX bs bs') (y : Loc) (Y : BRec)
    (hy : bs !! y = some Y) : ∃ Y', bs' !! y = some Y' ∧ derefStarX Y Y' := by
  obtain ⟨Y', hY'⟩ := Option.isSome_iff_exists.1 ((h.1 y).1 (by rw [hy]; rfl))
  exact ⟨Y', hY', h.2 y Y Y' hy hY'⟩

theorem derefMX_trans (A B C : GMap Loc BRec) (h : derefMX A B) (h' : derefMX B C) : derefMX A C := by
  refine ⟨fun y => (h.1 y).trans (h'.1 y), fun y Y Y'' hY hY'' => ?_⟩
  obtain ⟨Y', hY', hd⟩ := derefMX_get' A B h y Y hY
  exact derefStarX_trans Y Y' Y'' hd (h'.2 y Y' Y'' hY' hY'')

/-- A child `c` of `x` (record `B`), called with the buckets but `x` (dereferenced to `R`). -/
theorem child_preX (dep : Loc → Nat) (txl x : Loc) (bs R : GMap Loc BRec) (B : BRec)
    (name : GoString) (c : Loc) (hB : bs !! x = some B) (hdep : depOK dep bs)
    (hready : readyAtX bs x) (htx : txOK txl bs) (hR : derefMX (GMap.delete x bs) R)
    (hc : B.bm !! name = some c) :
    dep c < dep x ∧ depOK dep R ∧ readyAtX R c ∧ txOK txl R := by
  have hcx := hdep x B name c hB hc
  have hRb : ∀ y Y', R !! y = some Y' → ∃ Y, bs !! y = some Y ∧ y ≠ x ∧ derefStarX Y Y' := by
    intro y Y' hy
    obtain ⟨Y, hY, hd⟩ := derefMX_get _ R hR y Y' hy
    have hne : x ≠ y := by intro e; subst e; rw [GMap.lookup_delete] at hY; cases hY
    rw [GMap.lookup_delete_ne _ hne] at hY
    exact ⟨Y, hY, Ne.symm hne, hd⟩
  have hdR : depOK dep R := by
    intro y Y' n0 c0 hy hc0
    obtain ⟨Y, hY, -, hd⟩ := hRb y Y' hy
    rw [(derefStarX_bm Y Y' hd).1] at hc0
    exact hdep y Y n0 c0 hY hc0
  refine ⟨hcx, hdR, ?_, ?_⟩
  · intro y hr
    have hr' : reachB bs c y := reach_transfer dep R bs hdR (dep c) (fun y Y' _ hy => by
      obtain ⟨Y, hY, -, hd⟩ := hRb y Y' hy
      exact ⟨Y, hY, (derefStarX_bm Y Y' hd).1.symm⟩) (Nat.le_refl _) hr
    obtain ⟨Y, hY, hrd⟩ := hready y (reach_head bs B name hB hc hr')
    have hyx : x ≠ y := by
      intro e; subst e; have := reach_dep dep bs hdep hr'; omega
    obtain ⟨Y', hY', hd⟩ := derefMX_get' _ R hR y Y (by rw [GMap.lookup_delete_ne _ hyx]; exact hY)
    exact ⟨Y', hY', derefStarX_ready y Y Y' hrd hd⟩
  · intro y Y' hy
    obtain ⟨Y, hY, -, hd⟩ := hRb y Y' hy
    rw [(derefStarX_bm Y Y' hd).2]; exact htx y Y hY

/-- After a child's call: the buckets dereferenced so far, and those the call reached. -/
theorem child_postX (dep : Loc → Nat) (R0 R R' : GMap Loc BRec) (c : Loc) (hdep : depOK dep R0)
    (hR : derefMX R0 R) (hR' : derefMX R R') (hF : derefFromX R R' c) :
    derefMX R0 R' ∧ derefFromX R0 R' c ∧ ∀ c', derefFromX R0 R c' → derefFromX R0 R' c' := by
  refine ⟨derefMX_trans R0 R R' hR hR', ?_, ?_⟩
  · intro y hr
    have hr' : reachB R c y := reach_transfer dep R0 R hdep (dep c) (fun y Y _ hy => by
      obtain ⟨Y', hY', hd⟩ := derefMX_get' R0 R hR y Y hy
      exact ⟨Y', hY', (derefStarX_bm Y Y' hd).1⟩) (Nat.le_refl _) hr
    obtain ⟨Yi, Y'', hYi, hY'', hd⟩ := hF y hr'
    obtain ⟨Y, hY, hs⟩ := derefMX_get R0 R hR y Yi hYi
    exact ⟨Y, Y'', hY, hY'', star_bktX Y Yi Y'' hs hd⟩
  · intro c' hF' y hr
    obtain ⟨Y, Yi, hY, hYi, hd⟩ := hF' y hr
    obtain ⟨Y'', hY'', hs⟩ := derefMX_get' R R' hR' y Yi hYi
    exact ⟨Y, Y'', hY, hY'', bkt_starX Y Yi Y'' hd hs⟩

/-- After the children's calls: `x` and the buckets reachable from it are dereferenced. -/
theorem finalX (dep : Loc → Nat) (x : Loc) (bs R : GMap Loc BRec) (B B1 : BRec)
    (hB : bs !! x = some B) (hdep : depOK dep bs) (hbkt : derefBktX B B1)
    (hR : derefMX (GMap.delete x bs) R)
    (hall : ∀ name c, B.bm !! name = some c → derefFromX (GMap.delete x bs) R c) :
    derefMX bs (<[x := B1]> R) ∧ derefFromX bs (<[x := B1]> R) x := by
  refine ⟨⟨fun y => ?_, fun y Y Y' hY hY' => ?_⟩, fun y hr => ?_⟩
  · by_cases e : x = y
    · subst e; rw [hB, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ e, ← hR.1 y, GMap.lookup_delete_ne _ e]
  · by_cases e : x = y
    · subst e; rw [hB] at hY; cases hY; rw [GMap.lookup_insert] at hY'; cases hY'
      exact Or.inr hbkt
    · rw [GMap.lookup_insert_ne _ _ e] at hY'
      exact hR.2 y Y Y' (by rw [GMap.lookup_delete_ne _ e]; exact hY) hY'
  · rcases reach_split bs hr with rfl | ⟨X, name, c, hX, hc, hr'⟩
    · exact ⟨B, B1, hB, GMap.lookup_insert _ _ _, hbkt⟩
    rw [hB] at hX; cases hX
    have hcx := hdep x B name c hB hc
    have hr2 : reachB (GMap.delete x bs) c y :=
      reach_transfer dep bs _ hdep (dep c) (fun z Z hz hZ => by
        have hne : x ≠ z := by intro e; subst e; omega
        exact ⟨Z, by rw [GMap.lookup_delete_ne _ hne]; exact hZ, rfl⟩) (Nat.le_refl _) hr'
    have hyx : x ≠ y := by
      intro e; subst e; have := reach_dep dep bs hdep hr'; omega
    obtain ⟨Y, Y', hY, hY', hd⟩ := hall name c hc y hr2
    rw [GMap.lookup_delete_ne _ hyx] at hY
    exact ⟨Y, Y', hY, by rw [GMap.lookup_insert_ne _ _ hyx]; exact hY', hd⟩

/-- What the transaction's call is given. -/
theorem top_preX (T : WTx) (rl : Loc) (h : derefReadyX T rl) :
    ∃ dep, depOK dep T.bs ∧ readyAtX T.bs rl := by
  obtain ⟨hrl, -, ⟨dep, hdep⟩, hb⟩ := h
  refine ⟨dep, fun y Y name c hY hc => hdep y Y name c hY hc, fun y hr => ?_⟩
  have hin : (T.bs !! y).isSome := by
    cases hr with
    | root => exact hrl
    | child y0 Y0 name _ _ hY0 hc => exact (hb y0 Y0 hY0).2 name _ hc
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hin
  exact ⟨Y, hY, (hb y Y hY).1⟩

/-- What the transaction's call does. -/
theorem top_postX (T : WTx) (rl : Loc) (bs' : GMap Loc BRec) (st' : TxStats) (h : derefReadyX T rl)
    (hM : derefMX T.bs bs') (hF : derefFromX T.bs bs' rl) :
    derefRelX T { T with bs := bs', t := { T.t with stats' := st' } } := by
  refine ⟨rfl, rfl, rfl, rfl, hM.1, fun bl B B' hB hB' => ?_⟩
  obtain ⟨Y, Y', hY, hY', hd⟩ := hF bl (bktReach_reachB T rl bl (h.2.1 bl (by rw [hB]; rfl)))
  rw [hB] at hY; cases hY
  change bs' !! bl = some B' at hB'
  rw [hB'] at hY'; cases hY'
  exact hd


/-- A bucket's own step: its tree's nodes dereferenced and the root's parent chain outside it
kept (`M`), the others dropped. -/
theorem own_stepX (B : BRec) (S p : List Loc) (top : Loc) (M : GMap Loc NRec)
    (hu : upPath B.ns B.bv.rootNode' p top) (hk : kidsTree B.ns top S)
    (hSdom : ∀ l, l ∈ S ∨ l ∈ p → (B.ns !! l).isSome)
    (hdom : ∀ l, (M !! l).isSome ↔ (B.ns !! l).isSome)
    (hM : ∀ l r', M !! l = some r' → ∃ r, B.ns !! l = some r ∧ dnX3 r r')
    (hlive : ∀ l, l ∈ S ∨ l ∈ p → ∀ r r', B.ns !! l = some r → M !! l = some r' → dnX r r') :
    derefBktX B { B with ns := M, isrc := staleOf B.isrc } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hM, fun _ S' p' top' hu' _ hk' _ l hl => ?_,
    fun l h => (hdom l).2 h⟩
  obtain ⟨rfl, rfl⟩ := upPath_det B.ns hu hu'
  have e := kidsTree_det B.ns S.length top S S' (Nat.le_refl _) hk hk'
  subst e
  exact ⟨(hdom l).2 (hSdom l hl), hlive l hl⟩

/-- A bucket without a root node: its nodes made stale. -/
theorem own_step_nilX (B : BRec) (hn : B.bv.rootNode' = null) :
    derefBktX B { B with ns := Iris.Std.PartialMap.map staleRec B.ns, isrc := staleOf B.isrc } := by
  have hlk : ∀ l, (Iris.Std.PartialMap.map staleRec B.ns : GMap Loc NRec) !! l = (B.ns !! l).map staleRec := by
    intro l
    change Iris.Std.PartialMap.get? (Iris.Std.PartialMap.map staleRec B.ns) l = _
    rw [Iris.Std.LawfulPartialMap.get?_map (M := GMap Loc)]; rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun l r' h => ?_, fun h => absurd hn h, fun l h => ?_⟩
  · change (Iris.Std.PartialMap.map staleRec B.ns : GMap Loc NRec) !! l = some r' at h
    rw [hlk] at h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨r, hr, Or.inr (Or.inr rfl)⟩
  · show ((Iris.Std.PartialMap.map staleRec B.ns : GMap Loc NRec) !! l).isSome
    rw [hlk]; cases hb : B.ns !! l <;> simp_all

/-- A dereferenced transaction (`derefRelX`) keeps no byte of the view. -/
theorem noView_of_derefRelX (T T' : WTx) (h : derefRelX T T') : noView T' := by
  obtain ⟨-, -, -, -, hdom, hb⟩ := h
  intro bl B' hB'
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 ((hdom bl).2 (by rw [hB']; rfl))
  obtain ⟨-, -, -, -, -, hsrc, hns, -⟩ := hb bl B B' hB hB'
  refine ⟨?_, fun l r' hr' => ?_⟩
  · rw [hsrc]; cases B.isrc <;> simp [staleOf]
  · obtain ⟨r, -, hd⟩ := hns l r' hr'
    exact dnX3_noView r r' hd

/-- Each node of `bs'` keeps the struct (but its key) it has in `bs`. -/
def keepM (bs bs' : GMap Loc BRec) : Prop :=
  ∀ y Y Y' l r r', bs !! y = some Y → bs' !! y = some Y' → Y.ns !! l = some r →
    Y'.ns !! l = some r' → r'.nv = { r.nv with key' := r'.nv.key' }

theorem keepM_refl (bs : GMap Loc BRec) : keepM bs bs := by
  intro y Y Y' l r r' hY hY' hr hr'
  rw [hY] at hY'; cases hY'; rw [hr] at hr'; cases hr'; rfl

theorem derefStarX_ns (Y Y' : BRec) (h : derefStarX Y Y') (l : Loc) (r' : NRec)
    (hr' : Y'.ns !! l = some r') : ∃ r, Y.ns !! l = some r := by
  rcases h with rfl | h
  · exact ⟨r', hr'⟩
  · obtain ⟨r, hr, -⟩ := h.2.2.2.2.2.2.1 l r' hr'
    exact ⟨r, hr⟩

theorem keepM_trans (A B C : GMap Loc BRec) (hAB : derefMX A B) (hBC : derefMX B C)
    (h1 : keepM A B) (h2 : keepM B C) : keepM A C := by
  intro y Y Y'' l r r'' hY hY'' hr hr''
  obtain ⟨Y', hY', hd⟩ := derefMX_get' A B hAB y Y hY
  obtain ⟨r', hr'⟩ := derefStarX_ns Y' Y'' (hBC.2 y Y' Y'' hY' hY'') l r'' hr''
  rw [h2 y Y' Y'' l r' r'' hY' hY'' hr' hr'', h1 y Y Y' l r r' hY hY' hr hr']

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node_deref_accX (W : WView) (hc : W.data.locCar ≠ 0) (bl l : Loc) (r : NRec) (f : Qp)
    (g : Loc → DerefIn) (hg : g l = dIn r f) (hok : derefOK bl r) :
    nodeOwnX (GF := GF) W l r ∗ pagesView W.data W.ps f W.pages ⊢
      qPre g bl l ∗ (qPost g bl l -∗ ∃ nv' ins',
        ⌜derefNodeX r (derefRec r nv' ins') ∧ nv' = { r.nv with key' := nv'.key' }⌝ ∗
        nodeOwnX W l (derefRec r nv' ins') ∗ pagesView W.data W.ps f W.pages) := by
  obtain ⟨hbl, hlen, hws, hkey⟩ := hok
  have hlive : wsLive r.ws := fun w hw => ⟨(hws w hw).1, (hws w hw).2.1⟩
  have hkeys : ∀ i < (borrowEs r.ws f.half).length, 0 < (entryKey (borrowEs r.ws f.half) i).length := by
    intro i hi
    rw [wMatch_key _ _ (borrowEs_match r.ws f.half)]
    rw [borrowEs_length] at hi
    rw [wKey_get r.ws i hi]
    exact (hws _ (List.getElem_mem hi)).2.2
  iintro ⟨Hnd, Hpv⟩
  isimp only [nodeOwnX] at Hnd
  icases Hnd with ⟨Hn, Hins, Hents, Hch, Hchcap, Hkey⟩
  icases (pv_half W.data W.ps W.pages f).1 $$ Hpv with ⟨Hpk, Hpe⟩
  icases nodeBorrowD W hc r.ws r.ins f.half hlive $$ [Hpe Hents] with ⟨Hes, Hesback⟩
  · iframe
  unfold qPre qPost derefPreW derefPostW
  rw [hg]
  simp only [dIn]
  -- the new node's resources, from what `dereference` gives back
  have Hnew : ∀ (nv' : node) (insN : List Inode), nv' = { r.nv with key' := nv'.key' } →
      (l ↦ nv' ∗ nv'.children' ↦* r.cs ∗ nv'.inodes' ↦* insN ∗
        inodesOwn insN ((borrowEs r.ws f.half).map freshEntry) ∗
        ownSliceCap Loc r.nv.children' (DFrac.own 1) ∗
        (⌜nv'.key' = slice.nil⌝ ∨ nv'.key' ↦* r.key) : IProp GF) ⊢
      nodeOwnX W l (derefRec r nv' insN) := by
    intro nv' insN Hnv'
    have Hni : nv'.inodes' = r.nv.inodes' := by rw [Hnv']
    have Hnc : nv'.children' = r.nv.children' := by rw [Hnv']
    iintro ⟨Hn', Hch', HinsN, HesN, Hchcap, Hk⟩
    unfold nodeOwnX derefRec
    simp only
    rw [Hni, Hnc]
    rw [← Hni, ← Hnc]
    iframe
    isplitl [HesN]
    · iapply fresh_wOwn W insN r.ws _ (borrowEs_match r.ws f.half)
      iexact HesN
    icases Hk with (%Hkn | Hk)
    · rw [if_pos Hkn]; ipureintro; trivial
    · by_cases hkn : nv'.key' = slice.nil
      · rw [if_pos hkn]; ipureintro; trivial
      · rw [if_neg hkn]; unfold srcOwn; iexact Hk
  have Hrel : ∀ (nv' : node) (insN : List Inode), nv' = { r.nv with key' := nv'.key' } →
      (r.nv.key' = slice.nil → nv'.key' = slice.nil) → insN.length = r.ws.length →
      derefNode r (derefRec r nv' insN) := by
    intro nv' insN Hnv' Hkk Hil
    refine ⟨?_, rfl, rfl, rfl, Hkk, rfl, by simp [derefRec, Hil]⟩
    simp only [derefRec]
    rw [Hnv']
  by_cases hk : r.nv.key' = slice.nil
  · rw [if_pos hk] at *
    isplitl [Hn Hch Hins Hes]
    · iexists r.nv
      iframe
      isplitl []
      · ipureintro; exact ⟨rfl, hbl, hkeys⟩
      ileft; ipureintro; exact hk
    iintro ⟨%nv', Hn', Hch', %Hnv', ⟨%insN, HinsN, HesN⟩, Hold, Hkd⟩
    ihave %HiL := inodesOwn_length _ _ $$ HesN
    have HiL' : insN.length = r.ws.length := by rw [HiL]; simp [borrowEs_length]
    ihave Hb := Hesback $$ Hold
    icases Hb with ⟨Hpe, -⟩
    iexists nv', insN
    icases Hkd with (%Hkn | ⟨%Hkn, -, -⟩)
    · isplitr
      · ipureintro; exact ⟨⟨Hrel nv' insN Hnv' (fun _ => Hkn.2) HiL', fun h => absurd hk h⟩, Hnv'⟩
      isplitl [Hn' Hch' HinsN HesN Hchcap]
      · iapply Hnew nv' insN Hnv'
        iframe
        ileft; ipureintro; exact Hkn.2
      iapply (pv_half W.data W.ps W.pages f).2
      iframe
    · exact absurd hk Hkn
  · rw [if_neg hk]
    have hks : r.ksrc ≠ Src.stale := by
      rcases hkey with h | ⟨h, -⟩
      · exact absurd h hk
      · exact h
    have hkp : r.nv.pgid' = W64 0 ∨ 0 < r.key.length := by
      rcases hkey with h | ⟨-, h⟩
      · exact absurd h hk
      · exact h
    icases srcBorrowD W hc f.half r.nv.key' r.ksrc r.key hks $$ [Hpk Hkey] with ⟨Hk, Hkback⟩
    · iframe
    isplitl [Hn Hch Hins Hes Hk]
    · iexists r.nv
      iframe
      isplitl []
      · ipureintro; exact ⟨rfl, hbl, hkeys⟩
      iright
      iframe
      ipureintro; exact hkp
    iintro ⟨%nv', Hn', Hch', %Hnv', ⟨%insN, HinsN, HesN⟩, Hold, Hkd⟩
    ihave %HiL := inodesOwn_length _ _ $$ HesN
    have HiL' : insN.length = r.ws.length := by rw [HiL]; simp [borrowEs_length]
    ihave Hb := Hesback $$ Hold
    icases Hb with ⟨Hpe, -⟩
    iexists nv', insN
    icases Hkd with (%Hkn | ⟨-, Hko, Hkn⟩)
    · exact absurd Hkn.1 hk
    ihave Hb := Hkback $$ Hko
    icases Hb with ⟨Hpk, -⟩
    ihave %Hkl := ownSlice_len _ _ _ $$ Hkn
    have Hkx : 0 < r.key.length → nv'.key' ≠ slice.nil := by
      intro hpos he
      rw [he] at Hkl
      have : sint.nat (slice.nil : GoSlice).len = 0 := rfl
      omega
    isplitr
    · ipureintro; exact ⟨⟨Hrel nv' insN Hnv' (fun h => absurd h hk) HiL', fun _ hl => Hkx hl⟩, Hnv'⟩
    isplitl [Hn' Hch' HinsN HesN Hchcap Hkn]
    · iapply Hnew nv' insN Hnv'
      iframe
    iapply (pv_half W.data W.ps W.pages f).2
    iframe

/-- The nodes of a parent chain, out of the bucket's nodes (for `node.root`), and back. -/
theorem chain_accX (W : WView) (ns : GMap Loc NRec) :
    ∀ (l : Loc) (p : List Loc) (t : Loc), upPath ns l p t → p.Nodup → ∀ (m : GMap Loc NRec),
    (∀ x ∈ p, m !! x = ns !! x) →
    ([∗map] x ↦ r ∈ m, nodeOwnX (GF := GF) W x r) ⊢
      ([∗list] y ∈ chainList ns p, y.1 ↦ y.2) ∗
      (([∗list] y ∈ chainList ns p, y.1 ↦ y.2) -∗ [∗map] x ↦ r ∈ m, nodeOwnX (GF := GF) W x r) := by
  intro l p t h
  induction h with
  | self l r hr hp =>
    intro _ m hm
    have hm' := (hm l List.mem_cons_self).trans hr
    iintro H
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun x r => nodeOwnX (GF := GF) W x r)
      (show Std.get? m l = some r from hm')).1 $$ H with ⟨Hl, Hback⟩
    isimp only [nodeOwnX] at Hl
    icases Hl with ⟨Hn, Hrest⟩
    simp only [chainList, List.map_cons, List.map_nil, hr, Option.map_some, Option.getD_some]
    isplitl [Hn]
    · iapply BigSepL.bigSepL_cons.2
      iframe
      iapply BigSepL.bigSepL_nil.2; iempintro
    iintro Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hn, -⟩
    iapply Hback
    unfold nodeOwnX; iframe
  | up l r p t hr hp hu ih =>
    intro hnd m hm
    have hm' := (hm l List.mem_cons_self).trans hr
    have hl : l ∉ p := (List.nodup_cons.1 hnd).1
    iintro H
    icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun x r => nodeOwnX (GF := GF) W x r)
      (show Std.get? m l = some r from hm')).1 $$ H with ⟨Hl, H⟩
    isimp only [nodeOwnX] at Hl
    icases Hl with ⟨Hn, Hrest⟩
    have hm2 : ∀ x ∈ p, (Std.delete m l) !! x = ns !! x := by
      intro x hx
      have hne : l ≠ x := fun e => hl (e ▸ hx)
      change (GMap.delete l m) !! x = ns !! x
      rw [GMap.lookup_delete_ne _ hne]; exact hm x (List.mem_cons_of_mem _ hx)
    icases ih (List.nodup_cons.1 hnd).2 (Std.delete m l) hm2 $$ H with ⟨Hc, Hcback⟩
    have he : chainList ns (l :: p) = (l, r.nv) :: chainList ns p := by
      simp [chainList, hr]
    rw [he]
    isplitl [Hn Hc]
    · iapply BigSepL.bigSepL_cons.2
      iframe
    iintro Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hn, Hc⟩
    ihave H := Hcback $$ Hc
    iapply (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun x r => nodeOwnX (GF := GF) W x r)
      (show Std.get? m l = some r from hm')).2
    iframe
    unfold nodeOwnX; iframe

/-- Some entries of a map, as a list, and the rest of the map. -/
theorem map_split {V : Type} (Φ : Loc → V → IProp GF) : ∀ (Q : List Loc) (m : GMap Loc V), Q.Nodup →
    (∀ l ∈ Q, (m !! l).isSome) →
    ([∗map] l ↦ v ∈ m, Φ l v) ⊢ ([∗list] l ∈ Q, ∃ v, ⌜m !! l = some v⌝ ∗ Φ l v) ∗
      ∃ (m' : GMap Loc V), ⌜∀ l, m' !! l = if l ∈ Q then none else m !! l⌝ ∗ [∗map] l ↦ v ∈ m', Φ l v
  | [], m, _, _ => by
    iintro H
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iexists m
    iframe
    ipureintro; intro l; simp
  | x :: xs, m, hnd, hdom => by
    have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
    cases h : m !! x with
    | none =>
      have := hdom x List.mem_cons_self; rw [h] at this; cases this
    | some v =>
      iintro H
      icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := Φ) (show Std.get? m x = some v from h)).1 $$ H
        with ⟨Hx, H⟩
      have hdom' : ∀ l ∈ xs, ((Std.delete m x) !! l).isSome := by
        intro l hl
        have hne : x ≠ l := fun e => hx (e ▸ hl)
        change ((GMap.delete x m) !! l).isSome
        rw [GMap.lookup_delete_ne _ hne]; exact hdom l (List.mem_cons_of_mem _ hl)
      icases map_split Φ xs (Std.delete m x) (List.nodup_cons.1 hnd).2 hdom' $$ H with ⟨H, %m', %hm', Hm'⟩
      isplitl [Hx H]
      · iapply BigSepL.bigSepL_cons.2
        isplitl [Hx]
        · iexists v; iframe; ipureintro; exact h
        iapply (BigSepL.bigSepL_mono ?_) $$ H
        intro k l hl
        iintro ⟨%v', %hv', Hv⟩
        iexists v'; iframe; ipureintro
        have hne : x ≠ l := fun e => hx (e ▸ List.mem_of_getElem? hl)
        change (GMap.delete x m) !! l = some v' at hv'
        rw [GMap.lookup_delete_ne _ hne] at hv'; exact hv'
      iexists m'
      iframe
      ipureintro
      intro l
      rw [hm' l]
      by_cases e : x = l
      · subst e; simp [hx]
        change (GMap.delete x m) !! x = none
        exact GMap.lookup_delete _ _
      · change (if l ∈ xs then none else (GMap.delete x m) !! l) = _
        rw [GMap.lookup_delete_ne _ e]
        simp [List.mem_cons, Ne.symm e]

/-- A list of entries, added to a map without them. -/
theorem list_into_map {V : Type} (Φ : Loc → V → IProp GF) (P : Loc → V → Prop) :
    ∀ (Q : List Loc) (M : GMap Loc V), Q.Nodup → (∀ l ∈ Q, M !! l = none) →
    ([∗map] l ↦ v ∈ M, Φ l v) ∗ ([∗list] l ∈ Q, ∃ v, ⌜P l v⌝ ∗ Φ l v) ⊢ ∃ (M' : GMap Loc V),
      ⌜(∀ l, (M' !! l).isSome ↔ ((M !! l).isSome ∨ l ∈ Q)) ∧
        ∀ l v, M' !! l = some v → M !! l = some v ∨ P l v⌝ ∗ [∗map] l ↦ v ∈ M', Φ l v
  | [], M, _, _ => by
    iintro ⟨HM, -⟩
    iexists M
    iframe
    ipureintro
    exact ⟨fun l => by simp, fun l v h => Or.inl h⟩
  | x :: xs, M, hnd, hnone => by
    have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
    iintro ⟨HM, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%v, %hv, Hx⟩, H⟩
    have hMx : M !! x = none := hnone x List.mem_cons_self
    ihave HM := (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := Φ) (show Std.get? M x = none from hMx)).2 $$ [Hx HM]
    · iframe
    have hnone' : ∀ l ∈ xs, (<[x := v]> M) !! l = none := by
      intro l hl
      have hne : x ≠ l := fun e => hx (e ▸ hl)
      rw [GMap.lookup_insert_ne _ _ hne]; exact hnone l (List.mem_cons_of_mem _ hl)
    icases list_into_map Φ P xs (<[x := v]> M) (List.nodup_cons.1 hnd).2 hnone' $$ [HM H] with ⟨%M', %HM', HM⟩
    · iframe
    iexists M'
    iframe
    ipureintro
    obtain ⟨hd, hp⟩ := HM'
    refine ⟨fun l => ?_, fun l v' h => ?_⟩
    · rw [hd l]
      by_cases e : x = l
      · subst e; rw [GMap.lookup_insert]; simp
      · rw [GMap.lookup_insert_ne _ _ e]; simp [List.mem_cons, Ne.symm e]
    · rcases hp l v' h with h1 | h1
      · by_cases e : x = l
        · subst e; rw [GMap.lookup_insert] at h1; cases h1; exact Or.inr hv
        · rw [GMap.lookup_insert_ne _ _ e] at h1; exact Or.inl h1
      · exact Or.inr h1


/-- The tree of a bucket's nodes from `top` (its nodes `S`), lent to `dereference` (the view's
fraction `q` shared among them), and back: the nodes dereferenced (the others dropped). -/
theorem bkt_tree_accX (W : WView) (hc : W.data.locCar ≠ 0) (bl : Loc) (ns : GMap Loc NRec)
    (top : Loc) (S : List Loc) (hk : kidsTree ns top S)
    (hok : ∀ l ∈ S, ∃ r, ns !! l = some r ∧ derefOK bl r) (q : Qp) :
    pagesView (GF := GF) W.data W.ps q W.pages ∗ ([∗map] l ↦ r ∈ ns, nodeOwnX W l r) ⊢
      nodeTreeW (derefPreW (gOf ns S q) bl) (gOf ns S q) S.length top ∗
      (nodeTreeW (derefPostW (gOf ns S q) bl) (gOf ns S q) S.length top -∗
        ∃ (M : GMap Loc NRec), ⌜(∀ l, (M !! l).isSome ↔ (ns !! l).isSome) ∧
          ∀ l r', M !! l = some r' → ∃ r, ns !! l = some r ∧
            ((l ∈ S ∧ derefNodeK r r') ∨ (l ∉ S ∧ r' = staleRec r))⌝ ∗
          pagesView W.data W.ps q W.pages ∗ [∗map] l ↦ r ∈ M, nodeOwnX W l r) := by
  have hnd := kidsTree_nodup ns top S hk
  have hdom : ∀ l ∈ S, (ns !! l).isSome := by
    intro l hl; obtain ⟨r, hr, -⟩ := hok l hl; rw [hr]; rfl
  have hgcs : ∀ l ∈ S, ∃ r, ns !! l = some r ∧ (gOf ns S q l).cs = r.cs := by
    intro l hl; obtain ⟨r, hr, -⟩ := hok l hl
    exact ⟨r, hr, by simp [gOf, hr, dIn]⟩
  iintro ⟨Hpv, Hm⟩
  icases pv_list W S q hnd $$ Hpv with ⟨Hpl, Hpback⟩
  icases map_split (fun l r => nodeOwnX (GF := GF) W l r) S ns hnd hdom $$ Hm with ⟨Hl, %m', %Hm', Hrest⟩
  ihave Hb := (BigSepL.bigSepL_sep_eqv_symm).1 $$ [Hl Hpl]
  · iframe
  ihave Hb := (BigSepL.bigSepL_mono (Ψ := fun _ l => iprop(qPre (GF := GF) (gOf ns S q) bl l ∗
      (qPost (gOf ns S q) bl l -∗ ∃ r', ⌜∃ r, ns !! l = some r ∧ derefNodeK r r'⌝ ∗ nodeOwnX W l r' ∗
        pagesView W.data W.ps (fracOf S q l) W.pages))) ?_) $$ Hb
  · intro k l hl
    iintro ⟨⟨%r, %hr, Hn⟩, Hp⟩
    obtain ⟨r0, hr0, hok0⟩ := hok l (List.mem_of_getElem? hl)
    rw [hr] at hr0; cases hr0
    icases node_deref_accX W hc bl l r (fracOf S q l) (gOf ns S q) (by simp [gOf, hr]) hok0 $$ [Hn Hp]
      with ⟨Hpre, Hback⟩
    · iframe
    iframe Hpre
    iintro Hpost
    ihave H := Hback $$ Hpost
    icases H with ⟨%nv', %ins', %Hd, Hn, Hp⟩
    iexists (derefRec r nv' ins')
    iframe
    ipureintro; exact ⟨r, hr, Hd.1, by simp only [derefRec]; exact Hd.2⟩
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hb with ⟨Hpre, Hback⟩
  isimp only [qPre] at Hpre
  isimp only [qPost] at Hback
  isplitl [Hpre]
  · iapply (tree_of_list _ _ ns S.length top S (Nat.le_refl _) hk hgcs)
    iexact Hpre
  iintro Hpost
  ihave Hpost := (list_of_tree _ _ ns S.length top S hk hgcs) $$ Hpost
  ihave Hr := (BigSepL.bigSepL_wand) $$ Hpost Hback
  ihave Hr := (BigSepL.bigSepL_mono (Ψ := fun _ l => iprop((∃ r', ⌜∃ r, ns !! l = some r ∧ derefNodeK r r'⌝ ∗
      nodeOwnX (GF := GF) W l r') ∗ pagesView W.data W.ps (fracOf S q l) W.pages)) ?_) $$ Hr
  · intro k l _
    iintro ⟨%r', %Hd, Hn, Hp⟩
    iframe
    ipureintro; exact Hd
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hr with ⟨Hn, Hp⟩
  ihave Hpv := Hpback $$ Hp
  ihave Hn := (BigSepL.bigSepL_mono (Ψ := fun _ l => iprop(∃ r', ⌜l ∈ S ∧ ∃ r, ns !! l = some r ∧
      derefNodeK r r'⌝ ∗ nodeOwnX (GF := GF) W l r')) ?_) $$ Hn
  · intro k l hl
    iintro ⟨%r', %Hd, Hn⟩
    iexists r'
    iframe
    ipureintro; exact ⟨List.mem_of_getElem? hl, Hd⟩
  ihave Hrest := (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (Ψ := fun l r => nodeOwnX (GF := GF) W l (staleRec r)) (fun {_ _} _ => nodeOwnX_stale W _ _)) $$ Hrest
  ihave Hrest := (BiEntails.of_eq (BigSepM.bigSepM_map (M := GMap Loc)
    (Φ := fun l r => nodeOwnX (GF := GF) W l r) (m := m') (f := staleRec))).2 $$ Hrest
  have hlk : ∀ l, (Iris.Std.PartialMap.map staleRec m' : GMap Loc NRec) !! l = (m' !! l).map staleRec := by
    intro l
    change Iris.Std.PartialMap.get? (Iris.Std.PartialMap.map staleRec m') l = _
    rw [Iris.Std.LawfulPartialMap.get?_map (M := GMap Loc)]; rfl
  have hnoneS : ∀ l ∈ S, (Iris.Std.PartialMap.map staleRec m' : GMap Loc NRec) !! l = none := by
    intro l hl; rw [hlk, Hm' l, if_pos hl]; rfl
  icases list_into_map (fun l r => nodeOwnX (GF := GF) W l r)
    (fun l r' => l ∈ S ∧ ∃ r, ns !! l = some r ∧ derefNodeK r r') S
    (Iris.Std.PartialMap.map staleRec m') hnd hnoneS $$ [Hrest Hn] with ⟨%M, %HM, HM⟩
  · iframe
  iexists M
  iframe
  ipureintro
  refine ⟨fun l => ?_, fun l r' h => ?_⟩
  · rw [HM.1 l, hlk, Hm' l]
    by_cases hl : l ∈ S
    · rw [if_pos hl]; simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_or]
      exact ⟨fun _ => hdom l hl, fun _ => hl⟩
    · rw [if_neg hl]; simp only [Option.isSome_map, hl, or_false]
  · rcases HM.2 l r' h with h1 | ⟨hl, r, hr, hd⟩
    · rw [hlk] at h1
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h1
      have hl : l ∉ S := by intro hl; rw [Hm' l, if_pos hl] at hr; cases hr
      rw [Hm' l, if_neg hl] at hr
      exact ⟨r, hr, Or.inr ⟨hl, rfl⟩⟩
    · exact ⟨r, hr, Or.inl ⟨hl, hd⟩⟩

end own

end bbolt
end EtcdGrove
end Perennial
