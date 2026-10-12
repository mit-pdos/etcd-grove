/-
The clean invariant (`WriteTxModel.lean`'s `bktClean`) across `Bucket.node`: materializing a page
position (a child of a node, or the root) keeps a bucket clean (pure).
-/
module

public import Proof.go_etcd_io.bbolt.WriteCursorLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pages
variable [ext : FfiSyntax]

theorem pageWs_get (pg : List w8) (src : Src) (i : Nat) :
    (pageWs pg src)[i]? = if i < pageCount pg then some (pageW pg src i) else none := by
  unfold pageWs
  rw [List.getElem?_map]
  split
  · rw [List.getElem?_range ‹_›]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem pageWs_mem (pg : List w8) (src : Src) (w : WEntry) (h : w ∈ pageWs pg src) :
    ∃ i < pageCount pg, w = pageW pg src i := by
  unfold pageWs at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  exact ⟨i, List.mem_range.1 hi, rfl⟩

theorem wKey_pageWs_i (pg : List w8) (src : Src) (i : Nat) (h : i < pageCount pg) :
    wKey (pageWs pg src) i = (pageW pg src i).key := by
  unfold wKey; rw [pageWs_get, if_pos h]; rfl

theorem pageW_key_leaf (pg : List w8) (src : Src) (i : Nat) (h : pageFlags pg = leafPageFlag) :
    (pageW pg src i).key = leafKey pg i := by
  unfold pageW; rw [if_pos h]

theorem pageW_key_branch (pg : List w8) (src : Src) (i : Nat) (h : pageFlags pg ≠ leafPageFlag) :
    (pageW pg src i).key = branchKey pg i := by
  unfold pageW; rw [if_neg h]

/-- The entries of a well-formed page are sorted. -/
theorem pageWs_sorted (pg : List w8) (src : Src)
    (h : (pageFlags pg = leafPageFlag ∧ leafWF pg pg.length) ∨
      (pageFlags pg = branchPageFlag ∧ ∃ hwm, branchWF pg pg.length hwm)) :
    wsSorted (pageWs pg src) := by
  intro i j hij hj
  rw [pageWs_length] at hj
  rw [wKey_pageWs_i _ _ _ (by omega), wKey_pageWs_i _ _ _ hj]
  rcases h with ⟨hf, hw⟩ | ⟨hf, hwm, hw⟩
  · rw [pageW_key_leaf _ _ _ hf, pageW_key_leaf _ _ _ hf]
    exact hw.2.2.2 i j hij hj
  · have hne : pageFlags pg ≠ leafPageFlag := by rw [hf]; unfold branchPageFlag leafPageFlag; decide
    rw [pageW_key_branch _ _ _ hne, pageW_key_branch _ _ _ hne]
    exact hw.2.2.2.2 i j hij hj

/-- The keys of a good, well-formed page are non-empty. -/
theorem pageWs_keys (pg : List w8) (src : Src) (hg : pageGood pg)
    (h : (pageFlags pg = leafPageFlag ∧ leafWF pg pg.length) ∨
      (pageFlags pg = branchPageFlag ∧ ∃ hwm, branchWF pg pg.length hwm)) :
    ∀ w ∈ pageWs pg src, 0 < w.key.length := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := pageWs_mem pg src w hw
  rcases h with ⟨hf, hwf⟩ | ⟨hf, hwm, hwf⟩
  · rw [pageW_key_leaf _ _ _ hf]
    have hk := (hg.1 hf i hi).1
    have hb := (hwf.2.2.1 i hi).1
    unfold leafKey; rw [bytesAt_length _ _ _ (by omega)]; exact hk
  · have hne : pageFlags pg ≠ leafPageFlag := by rw [hf]; unfold branchPageFlag leafPageFlag; decide
    rw [pageW_key_branch _ _ _ hne]
    have hk := hg.2 hf i hi
    have hb := (hwf.2.2.2.1 i hi).1
    unfold branchKey; rw [bytesAt_length _ _ _ (by omega)]; exact hk

theorem pageWs_live (pg : List w8) (src : Src) (h : src ≠ Src.stale) : wsLive (pageWs pg src) := by
  intro w hw
  obtain ⟨i, -, rfl⟩ := pageWs_mem pg src w hw
  unfold pageW; split <;> exact ⟨h, by first | exact h | exact Src.noConfusion⟩

theorem isBktFlag_iff (x : Nat) (h : x < 2 ^ 32) :
    isBktFlag (W32 (x : Int)) ↔ x % 2 = bucketLeafFlag := by
  unfold isBktFlag bucketLeafFlag
  have h2 : (W32 (x : Int)).toNat = x := by
    rw [BitVec.toNat_ofInt]; simp; omega
  have hk : (W32 (x : Int) &&& W32 1).toNat = x % 2 := by
    rw [BitVec.toNat_and, h2]
    show x &&& 1 = x % 2
    rw [Nat.and_one_is_mod]
  constructor
  · intro hb
    refine Classical.byContradiction fun hc => hb ?_
    apply BitVec.eq_of_toNat_eq
    rw [hk]; simp; omega
  · intro hb he
    have := congrArg BitVec.toNat he
    rw [hk] at this; simp at this; omega

end pages

section frame
variable [ext : FfiSyntax]

/-- A node's well-formedness survives the bucket's growing by a node for the page `c`, which is
none of its children nor itself. -/
theorem nodeClean_frame (W : WView) (hwm : Nat) (bl : Loc) (B B' : BRec) (x : Loc) (r : NRec)
    (c : w64) (hib : B'.ib = B.ib) (hrn : B'.bv.rootNode' = B.bv.rootNode')
    (hnm : ∀ k, k ≠ c → B'.nm !! k = B.nm !! k)
    (hns : ∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧
      ry'.nv.parent' = ry.nv.parent' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws ∧
      ∀ z ∈ ry.cs, z ∈ ry'.cs)
    (hx : r.nv.isLeaf' = false → ∀ w ∈ r.ws, w.pgid ≠ c) (hpgid : r.nv.pgid' ≠ c)
    (h : nodeClean W hwm bl B x r) : nodeClean W hwm bl B' x r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, by rw [hnm _ hpgid]; exact h7, by rw [hib]; exact h8,
    by rw [hib]; exact h9, h10, h11, ?_, by rw [hrn]; exact h13, ?_, h15, ?_⟩
  · intro hl
    obtain ⟨a, b, hk⟩ := h12 hl
    refine ⟨a, b, fun w hw => ?_⟩
    obtain ⟨k1, k2, k3⟩ := hk w hw
    have hne := hx hl w hw
    refine ⟨k1, fun l' hl' => ?_, fun hn => k3 (by rw [← hnm _ hne]; exact hn)⟩
    rw [hnm _ hne] at hl'
    obtain ⟨r', hr', hp⟩ := k2 l' hl'
    obtain ⟨ry', hy', hp', -⟩ := hns l' r' hr'
    exact ⟨ry', hy', hp'.trans hp⟩
  · intro hp
    obtain ⟨rp, hrp, hleaf, hmem, w, hw, hwp⟩ := h14 hp
    obtain ⟨rp', hrp', -, hleaf', hws, hcs⟩ := hns _ rp hrp
    exact ⟨rp', hrp', hleaf'.trans hleaf, hcs x hmem, w, hws ▸ hw, hwp⟩
  · intro z hz
    obtain ⟨rc, hrc, hpc⟩ := h16 z hz
    obtain ⟨rc', hrc', hpc', -⟩ := hns z rc hrc
    exact ⟨rc', hrc', hpc'.trans hpc⟩

end frame

section add
variable [ext : FfiSyntax]

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α), l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons x xs ih =>
    intro hn h
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 hn
    refine List.nodup_cons.2 ⟨?_, ih hxs fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    intro hm
    obtain ⟨y, hy, hfy⟩ := List.mem_map.1 hm
    exact hx (h y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hfy ▸ hy)

theorem treeHas_mem (pages : GMap Nat (List w8)) (a d : Nat) (h : treeHas pages a d) :
    (pages !! d).isSome := by
  have key : ∀ a d, treeHas pages a d → (pages !! d).isSome := by
    intro a d h
    induction h using treeHas.rec
      (motive_2 := fun pg d _ => (pages !! d).isSome)
      (motive_3 := fun v d _ => (pages !! d).isSome) with
    | root root pg hpg => rw [hpg]; rfl
    | sub _ _ _ _ _ ih => exact ih
    | child _ _ _ _ _ _ ih => exact ih
    | bucket _ _ _ _ _ _ _ ih => exact ih
    | file _ _ _ _ ih => exact ih
    | inline _ _ _ _ ih => exact ih
  exact key a d h

theorem view_id_lt (W : WView) (hv : viewOK W) (d : Nat) (h : (W.pages !! d).isSome) :
    d < 2 ^ 48 := by
  obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 h
  have hb := (hv.2.2.2.1 d pg hpg)
  have hps := hv.2.1
  have : d * W.ps ≥ d * 80 := Nat.mul_le_mul_left d hps
  omega

theorem W64_eq_iff_nat (d : Nat) (c : w64) (hd : d < 2 ^ 64) :
    W64 (d : Int) = c ↔ d = uint.nat c := by
  constructor
  · intro h; rw [← h]; exact (uint_nat_W64_w d hd).symm
  · intro h; rw [h]; unfold uint.nat; word

theorem nodeAdded_ns (B : BRec) (c : w64) (nl l : Loc) (r : NRec) (cs' : GoSlice) (rp : NRec)
    (hnl : nl ≠ null) (hrp : B.ns !! nl = some rp) (y : Loc) :
    (nodeAdded B c nl l r cs').ns !! y =
      if y = l then some r
      else if y = nl then some { rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [l] }
      else B.ns !! y := by
  simp only [nodeAdded, parentAdd, hnl, ↓reduceIte, hrp]
  by_cases h1 : y = l
  · subst h1; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h1), if_neg h1]
    by_cases h2 : y = nl
    · subst h2; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h2), if_neg h2]

/-- Materializing the page position `c` (entry `i` of the branch node `nl`) keeps a bucket
clean. -/
theorem bktClean_addChild (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (l : Loc) (hfresh : B.ns !! l = none) (hl : l ≠ null)
    (hnl : nl ≠ null) (pg : List w8) (hpg : W.pages !! uint.nat w.pgid = some pg) (p : Loc)
    (s cs' : GoSlice) (src' : Src) (hsrc1 : src' = Src.view ∨ src' = Src.own DFrac.discard) :
    bktClean W hwm bl (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') := by
  have hsrc : src' ≠ Src.stale := by rcases hsrc1 with h | h <;> rw [h] <;> nofun
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hc
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc7 h0 nl rp hrp; rw [hbr] at this; cases this
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc3 h0).1; rw [this] at hrp; cases hrp
  have hNrp := hc8 nl rp hrp
  obtain ⟨-, -, -, -, -, -, hrp7, -, -, -, -, hrp12, -⟩ := id hNrp
  obtain ⟨-, -, hkids⟩ := hrp12 hbr
  have hwmem : w ∈ rp.ws := List.mem_of_getElem? hw
  obtain ⟨hclt, -, hcwf⟩ := hkids w hwmem
  have hwfc := hcwf hnone
  obtain ⟨hlen, hpid, -, hkind⟩ := treeWF_page _ _ _ pg hwfc hpg
  have hgood := hv.2.2.2.2.1 _ pg hpg
  have huniq := hv.2.2.2.2.2.1
  have hcid : W64 (pageId pg : Int) = w.pgid := by rw [hpid]; unfold uint.nat; word
  have hcself : treeHas W.pages (uint.nat w.pgid) (uint.nat w.pgid) := treeHas_self _ _ pg hpg
  have hpos : pagePosAt B nl i w.pgid := ⟨rp, w, hrp, hbr, hw, rfl, hnone⟩
  -- the maps of (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs')
  have hbv' : (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').bv = B.bv := by simp [nodeAdded, hnl]
  have hib' : (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').ib = B.ib := rfl
  have hnm' : ∀ k, (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! k = if k = w.pgid then some l else B.nm !! k := by
    intro k; show (<[w.pgid := l]> B.nm) !! k = _
    by_cases hk : k = w.pgid
    · subst hk; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]
  have hns' := nodeAdded_ns B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  have hlnl : l ≠ nl := by intro h; rw [h, hrp] at hfresh; cases hfresh
  have hpgc : rp.nv.pgid' ≠ w.pgid := by intro h; rw [h, hnone] at hrp7; cases hrp7
  -- the old nodes' records in (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs')
  have hnsB : ∀ y ry, B.ns !! y = some ry → ∃ ry', (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').ns !! y = some ry' ∧
      ry'.nv.parent' = ry.nv.parent' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws ∧
      ry'.nv.pgid' = ry.nv.pgid' ∧ ∀ z ∈ ry.cs, z ∈ ry'.cs := by
    intro y ry hy
    have hyl : y ≠ l := by intro h; rw [h, hfresh] at hy; cases hy
    by_cases hyn : y = nl
    · subst hyn; rw [hrp] at hy; cases hy
      refine ⟨({ rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [l] } : NRec), by rw [hns', if_neg hyl, if_pos rfl], rfl, rfl, rfl, rfl, fun z hz => ?_⟩
      exact List.mem_append_left _ hz
    · exact ⟨ry, by rw [hns', if_neg hyl, if_neg hyn]; exact hy, rfl, rfl, rfl, rfl, fun z hz => hz⟩
  -- positions of (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs')
  have hposB' : ∀ x j c', pagePosAt (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') x j c' →
      (x = l ∧ pageFlags pg = branchPageFlag ∧ j < pageCount pg ∧
        c' = W64 (branchPgid pg j : Int)) ∨ (pagePosAt B x j c' ∧ (x, j) ≠ (nl, i)) := by
    intro x j c' ⟨ry, wy, hy, hyleaf, hwy, hwyp, hnmy⟩
    rw [hnm'] at hnmy
    split at hnmy
    · cases hnmy
    rename_i hc'
    rw [hns'] at hy
    by_cases hxl : x = l
    · subst hxl; rw [if_pos rfl] at hy; cases hy
      left
      have hnleaf : pageFlags pg ≠ leafPageFlag := by
        intro h; simp [readNRec, readNodeV, h] at hyleaf
      have hbr' : pageFlags pg = branchPageFlag := by
        rcases hkind with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h hnleaf
        · exact h
      simp only [readNRec] at hwy
      rw [pageWs_get] at hwy
      split at hwy
      · cases hwy
        refine ⟨rfl, hbr', ‹_›, ?_⟩
        rw [← hwyp]; unfold pageW; rw [if_neg hnleaf]
      · cases hwy
    · rw [if_neg hxl] at hy
      right
      by_cases hxn : x = nl
      · subst hxn; rw [if_pos rfl] at hy; cases hy
        refine ⟨⟨rp, wy, hrp, hbr, hwy, hwyp, hnmy⟩, ?_⟩
        intro he
        simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        rw [hw] at hwy; cases hwy
        exact hc' hwyp.symm
      · rw [if_neg hxn] at hy
        refine ⟨⟨ry, wy, hy, hyleaf, hwy, hwyp, hnmy⟩, ?_⟩
        intro he; simp only [Prod.mk.injEq] at he; exact hxn he.1
  -- the subtree of a new position is inside c's, without w.pgid
  have hsub : ∀ j, j < pageCount pg → pageFlags pg = branchPageFlag → ∀ d,
      treeHas W.pages (uint.nat (W64 (branchPgid pg j : Int))) d → treeHas W.pages (uint.nat w.pgid) d := by
    intro j hj hb d hd
    rw [uint_nat_W64_w _ (branchPgid_lt pg j)] at hd
    exact treeHas_child _ _ pg hpg hb j hj d hd
  have hnotc : ∀ j, j < pageCount pg → pageFlags pg = branchPageFlag →
      ¬ treeHas W.pages (uint.nat (W64 (branchPgid pg j : Int))) (uint.nat w.pgid) := by
    intro j hj hb hd
    rw [uint_nat_W64_w _ (branchPgid_lt pg j)] at hd
    exact (huniq _ pg hpg hb).2 j hj hd
  have hmemlt : ∀ a d, treeHas W.pages a d → d < 2 ^ 64 := by
    intro a d h; have := view_id_lt W hv d (treeHas_mem _ _ _ h); omega
  refine ⟨fun h => absurd h hroot, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hroot, ?_, ?_, ?_⟩
  · rw [hbv']; exact hc2
  · rw [hbv']; intro h; exact absurd h hrn
  · rw [hbv']; intro h
    have h4 := hc4 h
    have hne : B.ib.root' ≠ w.pgid := by intro he; rw [he, hnone] at h4; cases h4
    rw [hnm', hib', if_neg hne]; exact h4
  · intro k l' hk
    rw [hnm'] at hk
    split at hk
    · rename_i hkc; cases hk
      refine ⟨hl, (readNRec bl nl p pg s src'), by rw [hns', if_pos rfl], ?_⟩
      rw [hkc]; exact hcid
    · obtain ⟨hl', r', hr', hp'⟩ := hc5 k l' hk
      obtain ⟨ry', hy', -, -, -, hpg', -⟩ := hnsB l' r' hr'
      exact ⟨hl', ry', hy', hpg'.trans hp'⟩
  · rw [hbv']; exact hc6
  · -- every node
    intro y ry hy
    rw [hns'] at hy
    by_cases hyl : y = l
    · -- the new node
      have hyl' := hyl.symm; subst hyl'; rw [if_pos rfl] at hy; cases hy
      have hkind' : (pageFlags pg = leafPageFlag ∧ leafWF pg pg.length) ∨
          (pageFlags pg = branchPageFlag ∧ ∃ hwm, branchWF pg pg.length hwm) := by
        rcases hkind with ⟨a, b, -⟩ | ⟨a, b, -⟩
        · exact Or.inl ⟨a, b⟩
        · exact Or.inr ⟨a, hwm, b⟩
      have hkeys := pageWs_keys pg src' hgood hkind'
      refine ⟨rfl, ?_, pageWs_sorted pg src' hkind', hkeys, pageWs_live pg src' hsrc, rfl, ?_,
        fun h => absurd h hroot, fun _ => ?_, ?_, ?_, ?_, fun h => absurd h hnl, fun _ => ?_,
        List.nodup_nil, fun z hz => absurd hz (List.not_mem_nil)⟩
      · simp [readNRec, inodesOf_length, pageWs_length]
      · show (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! W64 (pageId pg : Int) = some l
        rw [hcid, hnm', if_pos rfl]
      · show treeWF W.pages hwm (uint.nat (W64 (pageId pg : Int)))
        rw [hcid]; exact hwfc
      · show (if pageCount pg = 0 then slice.nil else (inodeOf p pg 0).key') = slice.nil ∨
          (0 < (wKey (pageWs pg src') 0).length ∧ src' ≠ Src.stale)
        split
        · exact Or.inl rfl
        · right
          refine ⟨?_, hsrc⟩
          rw [wKey_pageWs_i _ _ _ (by omega)]
          exact hkeys _ (by unfold pageWs; exact List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩)
      · intro hleaf w' hw' hbk
        have hfl : pageFlags pg = leafPageFlag := by
          simpa [readNRec, readNodeV] using hleaf
        obtain ⟨j, hj, rfl⟩ := pageWs_mem pg src' w' hw'
        simp only [pageW, hfl, ↓reduceIte] at hbk ⊢
        rw [isBktFlag_iff _ (by unfold leafFlags; exact leAt_lt _ _ 4)] at hbk
        rcases hkind with ⟨-, -, hbw⟩ | ⟨hb, -, -⟩
        · exact ⟨⟨hbw j hj hbk, fun h0 => (hgood.1 hfl j hj).2 hbk h0⟩, hsrc1⟩
        · rw [hb] at hfl; exact absurd hfl (by unfold branchPageFlag leafPageFlag; decide)
      · intro hleaf
        have hnleaf : pageFlags pg ≠ leafPageFlag := by
          intro h; simp [readNRec, readNodeV, h] at hleaf
        rcases hkind with ⟨h, -⟩ | ⟨hb, hbw, hbk⟩
        · exact absurd h hnleaf
        show 0 < (pageWs pg src').length ∧ ((pageWs pg src').map WEntry.pgid).Nodup ∧ _
        refine ⟨by rw [pageWs_length]; exact hbw.1, ?_, ?_⟩
        · have hmap : (pageWs pg src').map WEntry.pgid =
              (List.range (pageCount pg)).map fun j => W64 (branchPgid pg j : Int) := by
            unfold pageWs; rw [List.map_map]; congr 1; funext j
            simp [pageW, hnleaf]
          rw [hmap]
          refine nodup_map_on _ _ List.nodup_range ?_
          intro a ha b hb' hab
          have ha' := List.mem_range.1 ha
          have hb'' := List.mem_range.1 hb'
          refine Classical.byContradiction fun hne => ?_
          have hax : branchPgid pg a = branchPgid pg b := by
            have := congrArg uint.nat hab
            rwa [uint_nat_W64_w _ (branchPgid_lt _ _), uint_nat_W64_w _ (branchPgid_lt _ _)] at this
          cases hbk a ha' with
          | page _ pga _ hpga _ _ =>
            exact (huniq _ pg hpg hb).1 a b ha' hb'' hne _ (treeHas_self _ _ pga hpga)
              (hax ▸ treeHas_self _ _ pga hpga)
        · intro w' hw'
          obtain ⟨j, hj, rfl⟩ := pageWs_mem pg src' w' hw'
          have hpj : (pageW pg src' j).pgid = W64 (branchPgid pg j : Int) := by
            simp [pageW, hnleaf]
          rw [hpj]
          have hjne : W64 (branchPgid pg j : Int) ≠ w.pgid := by
            intro he
            apply hnotc j hj hb
            rw [he]; exact hcself
          have hjnone : B.nm !! W64 (branchPgid pg j : Int) = none := by
            have := hc10 nl i w.pgid hpos (branchPgid pg j) (treeHas_child _ _ pg hpg hb j hj _ (by
              cases hbk j hj with
              | page _ pgj _ hpgj _ _ => exact treeHas_self _ _ pgj hpgj))
            exact this
          refine ⟨by rw [uint_nat_W64_w _ (branchPgid_lt _ _)]; exact (hbw.2.2.2.1 j hj).2.2, ?_, ?_⟩
          · intro l' hl'; rw [hnm', if_neg hjne, hjnone] at hl'; cases hl'
          · intro _; rw [uint_nat_W64_w _ (branchPgid_lt _ _)]; exact hbk j hj
      · refine ⟨({ rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [l] } : NRec), by rw [hns', show (readNRec bl nl p pg s src').nv.parent' = nl from rfl, if_neg (Ne.symm hlnl),
          if_pos rfl], hbr,
          List.mem_append_right _ (List.mem_singleton_self _), w, hwmem, ?_⟩
        show w.pgid = W64 (pageId pg : Int); rw [hcid]
    · rw [if_neg hyl] at hy
      by_cases hyn : y = nl
      · -- the parent
        have hyn' := hyn.symm; subst hyn'; rw [if_pos rfl] at hy; cases hy
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hNrp
        refine ⟨h1, h2, h3, h4, h5, h6, ?_, by rw [hib']; exact h8, by rw [hib']; exact h9, h10, h11,
          ?_, by rw [hbv']; exact h13, ?_, ?_, ?_⟩
        · show (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! rp.nv.pgid' = some nl
          rw [hnm', if_neg hpgc]; exact h7
        · intro hb'
          obtain ⟨a, b, hk⟩ := h12 hb'
          refine ⟨a, b, fun w' hw' => ?_⟩
          obtain ⟨k1, k2, k3⟩ := hk w' hw'
          refine ⟨k1, fun l' hl' => ?_, fun hn => ?_⟩
          · rw [hnm'] at hl'
            split at hl'
            · cases hl'; exact ⟨(readNRec bl nl p pg s src'), by rw [hns', if_pos rfl], rfl⟩
            · obtain ⟨r', hr', hp'⟩ := k2 l' hl'
              obtain ⟨ry', hy', hpp, -⟩ := hnsB l' r' hr'
              exact ⟨ry', hy', hpp.trans hp'⟩
          · rw [hnm'] at hn
            split at hn
            · cases hn
            · exact k3 hn
        · intro hp
          obtain ⟨g, hg, hgl, hgm, wg, hwg, hwgp⟩ := h14 hp
          obtain ⟨g', hg', -, hgl', hgws, -, hgcs⟩ := hnsB _ g hg
          exact ⟨g', hg', hgl'.trans hgl, hgcs nl hgm, wg, hgws ▸ hwg, hwgp⟩
        · refine List.nodup_append.2 ⟨h15, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
          intro a ha b hb heq
          rw [List.mem_singleton] at hb
          subst hb; subst heq
          obtain ⟨rc, hrc, -⟩ := h16 _ ha
          rw [hfresh] at hrc; cases hrc
        · intro z hz
          rcases List.mem_append.1 hz with hz | hz
          · obtain ⟨rc, hrc, hpc⟩ := h16 z hz
            obtain ⟨rc', hrc', hpc', -⟩ := hnsB z rc hrc
            exact ⟨rc', hrc', hpc'.trans hpc⟩
          · rw [List.mem_singleton] at hz; subst hz
            exact ⟨(readNRec bl nl p pg s src'), by rw [hns', if_pos rfl], rfl⟩
      · -- another node
        rw [if_neg hyn] at hy
        refine nodeClean_frame W hwm bl B (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') y ry w.pgid hib' (by rw [hbv'])
          (fun k hk => by rw [hnm', if_neg hk]) (fun y' ry' hy' => ?_) ?_ ?_ (hc8 y ry hy)
        · obtain ⟨a, b, c1, d, e, -, f⟩ := hnsB y' ry' hy'
          exact ⟨a, b, c1, d, e, f⟩
        · intro hb' w' hw' he
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hw'
          have hposy : pagePosAt B y j w.pgid := ⟨ry, w', hy, hb', hj, he, hnone⟩
          exact hc9 y j w.pgid nl i w.pgid hposy hpos (by intro h; simp only [Prod.mk.injEq] at h; exact hyn h.1)
            _ hcself hcself
        · intro he
          obtain ⟨-, -, -, -, -, -, h7, -⟩ := hc8 y ry hy
          rw [he, hnone] at h7; cases h7
  · -- positions disjoint
    intro x1 j1 c1 x2 j2 c2 hp1 hp2 hne d hd1 hd2
    rcases hposB' x1 j1 c1 hp1 with ⟨rfl, hb, hj1, rfl⟩ | ⟨hq1, hn1⟩ <;>
      rcases hposB' x2 j2 c2 hp2 with ⟨rfl, hb2, hj2, rfl⟩ | ⟨hq2, hn2⟩
    · have hjne : j1 ≠ j2 := by intro h; exact hne (by rw [h])
      rw [uint_nat_W64_w _ (branchPgid_lt _ _)] at hd1 hd2
      exact (huniq _ pg hpg hb).1 j1 j2 hj1 hj2 hjne d hd1 hd2
    · exact hc9 nl i w.pgid x2 j2 c2 hpos hq2 (Ne.symm hn2) d (hsub j1 hj1 hb d hd1) hd2
    · exact hc9 x1 j1 c1 nl i w.pgid hq1 hpos hn1 d hd1 (hsub j2 hj2 hb2 d hd2)
    · exact hc9 x1 j1 c1 x2 j2 c2 hq1 hq2 hne d hd1 hd2
  · -- positions node-free
    intro x j c' hp d hd
    rw [hnm']
    split
    · rename_i hdc
      have hdlt := hmemlt _ _ hd
      rw [W64_eq_iff_nat _ _ hdlt] at hdc
      subst hdc
      rcases hposB' x j c' hp with ⟨rfl, hb, hj, rfl⟩ | ⟨hq, hn⟩
      · exact absurd hd (hnotc j hj hb)
      · exact absurd hcself (hc9 x j c' nl i w.pgid hq hpos hn _ hd)
    · rcases hposB' x j c' hp with ⟨rfl, hb, hj, rfl⟩ | ⟨hq, -⟩
      · exact hc10 nl i w.pgid hpos d (hsub j hj hb d hd)
      · exact hc10 x j c' hq d hd

end add

section kids
variable [ext : FfiSyntax]

/-- The stack elements `es` select, from position `pid` down to a leaf, a child at each level
(`wpath` without where each element points: what stays true as nodes are materialized). -/
def kpath (W : WView) (B : BRec) : w64 → List elemRef → Prop
  | _, [] => False
  | pid, [r] => 0 ≤ sint.Z r.index' ∧ ∃ ks, kidsAt W B pid = some (true, ks)
  | pid, r :: r2 :: rs => 0 ≤ sint.Z r.index' ∧ ∃ ks c,
      kidsAt W B pid = some (false, ks) ∧ ks[(sint.Z r.index').toNat]? = some c ∧
      kpath W B c (r2 :: rs)

theorem kpath_of_wpath (W : WView) (B : BRec) :
    ∀ (es : List elemRef) (pid : w64), wpath W B pid es → kpath W B pid es := by
  intro es
  induction es with
  | nil => intro pid h; exact h
  | cons r rs ih =>
    intro pid h
    cases rs with
    | nil => exact ⟨h.2.1, h.2.2⟩
    | cons r2 rs' =>
      obtain ⟨-, hi, ks, c, hk, hc, hrest⟩ := h
      exact ⟨hi, ks, c, hk, hc, ih c hrest⟩

theorem kpath_mono (W : WView) (B B' : BRec) (h : ∀ pid, kidsAt W B' pid = kidsAt W B pid) :
    ∀ (es : List elemRef) (pid : w64), kpath W B pid es → kpath W B' pid es := by
  intro es
  induction es with
  | nil => intro pid h; exact h
  | cons r rs ih =>
    intro pid hp
    cases rs with
    | nil => exact ⟨hp.1, by rw [h]; exact hp.2⟩
    | cons r2 rs' =>
      obtain ⟨hi, ks, c, hk, hc, hrest⟩ := hp
      exact ⟨hi, ks, c, by rw [h]; exact hk, hc, ih c hrest⟩

theorem pageWs_pgids (pg : List w8) (src : Src) (h : pageFlags pg ≠ leafPageFlag) :
    (pageWs pg src).map WEntry.pgid =
      (List.range (pageCount pg)).map fun i => W64 (branchPgid pg i : Int) := by
  unfold pageWs; rw [List.map_map]; congr 1; funext j; simp [pageW, h]

/-- Materializing the page position `c` changes no position's kind or children. -/
theorem kidsAt_addChild (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (c : w64)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hnone : B.nm !! c = none) (l : Loc) (hfresh : B.ns !! l = none)
    (hnl : nl ≠ null) (pg : List w8) (hpg : W.pages !! uint.nat c = some pg) (p : Loc)
    (s cs' : GoSlice) (src' : Src) :
    ∀ pid, kidsAt W (nodeAdded B c nl l (readNRec bl nl p pg s src') cs') pid = kidsAt W B pid := by
  obtain ⟨-, -, -, -, hc5, -, hc7, -, -, -⟩ := hc
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc7 h0 nl rp hrp; rw [hbr] at this; cases this
  have hns' := nodeAdded_ns B c nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  have hbv' : (nodeAdded B c nl l (readNRec bl nl p pg s src') cs').bv = B.bv := by
    simp [nodeAdded, hnl]
  intro pid
  have hres : ∀ B0 : BRec, B0.ib.root' ≠ W64 0 → resolve B0 pid = B0.nm !! pid := by
    intro B0 h; unfold resolve; rw [if_neg h]
  have hpa : wpageAt W (nodeAdded B c nl l (readNRec bl nl p pg s src') cs') pid = wpageAt W B pid := by
    unfold wpageAt; rw [hbv']; rfl
  unfold kidsAt
  rw [hres (nodeAdded B c nl l (readNRec bl nl p pg s src') cs') hroot, hres B hroot, hpa]
  show (match (<[c := l]> B.nm) !! pid with
    | some l => _ | none => _) = _
  by_cases hpc : pid = c
  · subst hpc
    rw [GMap.lookup_insert, hnone]
    dsimp only
    rw [hns', if_pos rfl]
    unfold wpageAt; rw [if_neg hroot, hpg]
    simp only [Option.map_some, readNRec, readNodeV]
    by_cases hf : pageFlags pg = leafPageFlag
    · simp [hf]
    · simp [hf, pageWs_pgids pg src' hf]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hpc)]
    cases hk : B.nm !! pid with
    | none => rfl
    | some l' =>
      obtain ⟨-, r', hr', -⟩ := hc5 pid l' hk
      have hl'l : l' ≠ l := by intro h; rw [h, hfresh] at hr'; cases hr'
      simp only
      rw [hns', if_neg hl'l]
      by_cases hl'n : l' = nl
      · subst hl'n; rw [if_pos rfl, hrp]; rfl
      · rw [if_neg hl'n]

end kids

section root
variable [ext : FfiSyntax]

theorem nodeAdded_root_ns (B : BRec) (c : w64) (l : Loc) (r : NRec) (cs' : GoSlice)
    (hns : B.ns = ∅) (y : Loc) :
    (nodeAdded B c null l r cs').ns !! y = if y = l then some r else none := by
  simp only [nodeAdded, parentAdd, ↓reduceIte, hns]
  by_cases h : y = l
  · subst h; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]; rfl

/-- Materializing the root of a bucket with no node keeps it clean. -/
theorem bktClean_addRoot (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (l : Loc) (hl : l ≠ null)
    (pg : List w8)
    (hpgf : B.ib.root' ≠ W64 0 → W.pages !! uint.nat B.ib.root' = some pg)
    (hpgi : B.ib.root' = W64 0 → pg = B.ipg) (p : Loc)
    (s cs' : GoSlice) (src' : Src) (hsrc1 : src' = Src.view ∨ src' = Src.own DFrac.discard) :
    bktClean W hwm bl (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') := by
  have hsrc : src' ≠ Src.stale := by rcases hsrc1 with h | h <;> rw [h] <;> nofun
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hc
  obtain ⟨hns0, hnm0⟩ := hc3 hrn
  have hns' := nodeAdded_root_ns B B.ib.root' l (readNRec bl null p pg s src') cs' hns0
  have hnm' : ∀ k, (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').nm !! k =
      if k = B.ib.root' then some l else none := by
    intro k; show (<[B.ib.root' := l]> B.nm) !! k = _
    by_cases hk : k = B.ib.root'
    · subst hk; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk, hnm0]; rfl
  have hbv' : (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').bv =
      { B.bv with rootNode' := l } := by simp [nodeAdded]
  have hib' : (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').ib = B.ib := rfl
  -- the page's facts
  obtain ⟨hlen, hpid, hkind, hgood, hinl⟩ : 16 ≤ pg.length ∧ W64 (pageId pg : Int) = B.ib.root' ∧
      ((pageFlags pg = leafPageFlag ∧ leafWF pg pg.length ∧
          ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag → bvalOK W.pages hwm (leafValue pg i)) ∨
       (pageFlags pg = branchPageFlag ∧ branchWF pg pg.length hwm ∧ B.ib.root' ≠ W64 0 ∧
          ∀ i < pageCount pg, treeWF W.pages hwm (branchPgid pg i))) ∧
      (∀ w ∈ pageWs pg src', 0 < w.key.length) ∧
      (B.ib.root' = W64 0 → pageFlags pg = leafPageFlag) := by
    by_cases hr : B.ib.root' = W64 0
    · obtain ⟨-, -, hg⟩ := hc1 hr hrn
      rw [hpgi hr]
      obtain ⟨hid, hfl, hwf, hl16, hks⟩ := hg
      refine ⟨hl16, by rw [hid, hr]; rfl, Or.inl ⟨hfl, hwf, fun i hi h => ?_⟩, ?_, fun _ => hfl⟩
      · have := (hks i hi).2; unfold bucketLeafFlag at h; omega
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := pageWs_mem _ src' w hw
        rw [pageW_key_leaf _ _ _ hfl]
        have hb := (hwf.2.2.1 i hi).1
        unfold leafKey; rw [bytesAt_length _ _ _ (by omega)]; exact (hks i hi).1
    · have hpg := hpgf hr
      obtain ⟨-, hwf⟩ := hc2 hr
      obtain ⟨hl16, hid, -, hk⟩ := treeWF_page _ _ _ pg (hwf hrn) hpg
      have hg := hv.2.2.2.2.1 _ pg hpg
      refine ⟨hl16, by rw [hid]; unfold uint.nat; word, ?_, ?_, fun h => absurd h hr⟩
      · rcases hk with ⟨a, b, c⟩ | ⟨a, b, c⟩
        · exact Or.inl ⟨a, b, fun i hi h => ⟨c i hi h, (hg.1 a i hi).2 h⟩⟩
        · exact Or.inr ⟨a, b, hr, c⟩
      · apply pageWs_keys pg src' hg
        rcases hk with ⟨a, b, -⟩ | ⟨a, b, -⟩
        · exact Or.inl ⟨a, b⟩
        · exact Or.inr ⟨a, hwm, b⟩
  have hmemlt : ∀ a d, treeHas W.pages a d → d < 2 ^ 64 := by
    intro a d h; have := view_id_lt W hv d (treeHas_mem _ _ _ h); omega
  have huniq := hv.2.2.2.2.2.1
  -- positions of the new bucket: the new node's children
  have hposB' : ∀ x j c', pagePosAt (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') x j c' →
      x = l ∧ pageFlags pg = branchPageFlag ∧ B.ib.root' ≠ W64 0 ∧ j < pageCount pg ∧
        c' = W64 (branchPgid pg j : Int) := by
    intro x j c' hpp
    obtain ⟨ry, wy, hy, hyleaf, hwy, hwyp, -⟩ := hpp
    rw [hns'] at hy
    split at hy
    · rename_i hxl; subst hxl; cases hy
      have hnleaf : pageFlags pg ≠ leafPageFlag := by
        intro h; simp [readNRec, readNodeV, h] at hyleaf
      rcases hkind with ⟨h, -⟩ | ⟨hb, -, hr, -⟩
      · exact absurd h hnleaf
      simp only [readNRec] at hwy
      rw [pageWs_get] at hwy
      split at hwy
      · cases hwy
        refine ⟨rfl, hb, hr, ‹_›, ?_⟩
        rw [← hwyp]; unfold pageW; rw [if_neg hnleaf]
      · cases hwy
    · cases hy
  refine ⟨fun _ h => absurd h (by rw [hbv']; exact hl), fun hr => ⟨(hc2 hr).1, fun h => absurd h
    (by rw [hbv']; exact hl)⟩, fun h => absurd h (by rw [hbv']; exact hl), fun _ => by
      rw [hnm', hib', if_pos rfl, hbv'], ?_, by rw [hbv']; exact hc6, ?_, ?_, ?_, ?_⟩
  · intro k l' hk
    rw [hnm'] at hk
    split at hk
    · rename_i hkr; cases hk
      exact ⟨hl, _, by rw [hns', if_pos rfl], by rw [hkr]; exact hpid⟩
    · cases hk
  · intro h0 y ry hy
    rw [hns'] at hy
    split at hy
    · cases hy; simp [readNRec, readNodeV, hinl h0]
    · cases hy
  · intro y ry hy
    rw [hns'] at hy
    split at hy
    · rename_i hyl; have hyl' := hyl.symm; subst hyl'; cases hy
      have hkind' : (pageFlags pg = leafPageFlag ∧ leafWF pg pg.length) ∨
          (pageFlags pg = branchPageFlag ∧ ∃ hwm, branchWF pg pg.length hwm) := by
        rcases hkind with ⟨a, b, -⟩ | ⟨a, b, -⟩
        · exact Or.inl ⟨a, b⟩
        · exact Or.inr ⟨a, hwm, b⟩
      refine ⟨rfl, ?_, pageWs_sorted pg src' hkind', hgood, pageWs_live pg src' hsrc, rfl, ?_,
        fun h0 => ?_, fun hr => ?_, ?_, ?_, ?_, fun _ => by rw [hbv'], fun h => absurd rfl h,
        List.nodup_nil, fun z hz => absurd hz (List.not_mem_nil)⟩
      · simp [readNRec, inodesOf_length, pageWs_length]
      · show (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').nm !!
          W64 (pageId pg : Int) = some l
        rw [hpid, hnm', if_pos rfl]
      · show W64 (pageId pg : Int) = W64 0; rw [hpid]; exact h0
      · show treeWF W.pages hwm (uint.nat (W64 (pageId pg : Int)))
        rw [hpid]; exact (hc2 hr).2 hrn
      · show (if pageCount pg = 0 then slice.nil else (inodeOf p pg 0).key') = slice.nil ∨
          (0 < (wKey (pageWs pg src') 0).length ∧ src' ≠ Src.stale)
        split
        · exact Or.inl rfl
        · right
          refine ⟨?_, hsrc⟩
          rw [wKey_pageWs_i _ _ _ (by omega)]
          exact hgood _ (by unfold pageWs; exact List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩)
      · intro hleaf w' hw' hbk
        have hfl : pageFlags pg = leafPageFlag := by
          simpa [readNRec, readNodeV] using hleaf
        obtain ⟨j, hj, rfl⟩ := pageWs_mem pg src' w' hw'
        simp only [pageW, hfl, ↓reduceIte] at hbk ⊢
        rw [isBktFlag_iff _ (by unfold leafFlags; exact leAt_lt _ _ 4)] at hbk
        rcases hkind with ⟨-, -, hbw⟩ | ⟨hb, -, -⟩
        · exact ⟨hbw j hj hbk, hsrc1⟩
        · rw [hb] at hfl; exact absurd hfl (by unfold branchPageFlag leafPageFlag; decide)
      · intro hleaf
        have hnleaf : pageFlags pg ≠ leafPageFlag := by
          intro h; simp [readNRec, readNodeV, h] at hleaf
        rcases hkind with ⟨h, -⟩ | ⟨hb, hbw, hr, hbk⟩
        · exact absurd h hnleaf
        have hpg := hpgf hr
        show 0 < (pageWs pg src').length ∧ ((pageWs pg src').map WEntry.pgid).Nodup ∧ _
        refine ⟨by rw [pageWs_length]; exact hbw.1, ?_, ?_⟩
        · rw [pageWs_pgids pg src' hnleaf]
          refine nodup_map_on _ _ List.nodup_range ?_
          intro a ha b hb' hab
          have ha' := List.mem_range.1 ha
          have hb'' := List.mem_range.1 hb'
          refine Classical.byContradiction fun hne => ?_
          have hax : branchPgid pg a = branchPgid pg b := by
            have := congrArg uint.nat hab
            rwa [uint_nat_W64_w _ (branchPgid_lt _ _), uint_nat_W64_w _ (branchPgid_lt _ _)] at this
          cases hbk a ha' with
          | page _ pga _ hpga _ _ =>
            exact (huniq _ pg hpg hb).1 a b ha' hb'' hne _ (treeHas_self _ _ pga hpga)
              (hax ▸ treeHas_self _ _ pga hpga)
        · intro w' hw'
          obtain ⟨j, hj, rfl⟩ := pageWs_mem pg src' w' hw'
          have hpj : (pageW pg src' j).pgid = W64 (branchPgid pg j : Int) := by
            simp [pageW, hnleaf]
          rw [hpj]
          have hjne : W64 (branchPgid pg j : Int) ≠ B.ib.root' := by
            intro he
            have hh := (huniq _ pg hpg hb).2 j hj
            apply hh
            have := congrArg uint.nat he
            rw [uint_nat_W64_w _ (branchPgid_lt _ _)] at this
            rw [← this]
            cases hbk j hj with
            | page _ pgj _ hpgj _ _ => exact treeHas_self _ _ pgj hpgj
          refine ⟨by rw [uint_nat_W64_w _ (branchPgid_lt _ _)]; exact (hbw.2.2.2.1 j hj).2.2, ?_, ?_⟩
          · intro l' hl'; rw [hnm', if_neg hjne] at hl'; cases hl'
          · intro _; rw [uint_nat_W64_w _ (branchPgid_lt _ _)]; exact hbk j hj
    · cases hy
  · intro x1 j1 c1 x2 j2 c2 hp1 hp2 hne d hd1 hd2
    obtain ⟨rfl, hb, hr, hj1, rfl⟩ := hposB' x1 j1 c1 hp1
    obtain ⟨rfl, -, -, hj2, rfl⟩ := hposB' _ j2 c2 hp2
    have hjne : j1 ≠ j2 := by intro h; exact hne (by rw [h])
    rw [uint_nat_W64_w _ (branchPgid_lt _ _)] at hd1 hd2
    exact (huniq _ pg (hpgf hr) hb).1 j1 j2 hj1 hj2 hjne d hd1 hd2
  · intro x j c' hp d hd
    obtain ⟨rfl, hb, hr, hj, rfl⟩ := hposB' x j c' hp
    rw [hnm']
    split
    · rename_i hdr
      have hdlt := hmemlt _ _ hd
      rw [W64_eq_iff_nat _ _ hdlt] at hdr
      subst hdr
      rw [uint_nat_W64_w _ (branchPgid_lt _ _)] at hd
      exact absurd hd ((huniq _ pg (hpgf hr) hb).2 j hj)
    · rfl

/-- Materializing the root (non-inline) changes no position's kind or children. -/
theorem kidsAt_addRoot (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (hroot : B.ib.root' ≠ W64 0)
    (l : Loc) (pg : List w8) (hpg : W.pages !! uint.nat B.ib.root' = some pg) (p : Loc)
    (s cs' : GoSlice) (src' : Src) :
    ∀ pid, kidsAt W (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') pid =
      kidsAt W B pid := by
  obtain ⟨-, -, hc3, -⟩ := hc
  obtain ⟨hns0, hnm0⟩ := hc3 hrn
  have hns' := nodeAdded_root_ns B B.ib.root' l (readNRec bl null p pg s src') cs' hns0
  intro pid
  have hres : ∀ B0 : BRec, B0.ib.root' ≠ W64 0 → resolve B0 pid = B0.nm !! pid := by
    intro B0 h; unfold resolve; rw [if_neg h]
  have hpa : wpageAt W (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') pid =
      wpageAt W B pid := by
    unfold wpageAt; simp [nodeAdded]
  unfold kidsAt
  rw [hres (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') hroot, hres B hroot, hpa]
  show (match (<[B.ib.root' := l]> B.nm) !! pid with
    | some l => _ | none => _) = _
  by_cases hpc : pid = B.ib.root'
  · subst hpc
    rw [GMap.lookup_insert, hnm0]
    dsimp only
    rw [hns', if_pos rfl]
    unfold wpageAt; rw [if_neg hroot, hpg]
    simp only [Option.map_some, readNRec, readNodeV]
    by_cases hf : pageFlags pg = leafPageFlag
    · simp [hf]
    · simp [hf, pageWs_pgids pg src' hf]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hpc), hnm0]; rfl

end root

section steps
variable [ext : FfiSyntax]

/-- The bucket `B'` is `B` with nodes materialized (its root node maybe set). -/
def bktGrows (B B' : BRec) : Prop :=
  B'.bm = B.bm ∧ B'.ib = B.ib ∧ B'.ipg = B.ipg ∧ ∃ rn, B'.bv = { B.bv with rootNode' := rn }

/-- A page of a well-formed tree, good, is one `ReadInodeFromPage` reads. -/
theorem pageReadable_of (pages : GMap Nat (List w8)) (hwm id : Nat) (pg : List w8)
    (h : treeWF pages hwm id) (hpg : pages !! id = some pg) (hg : pageGood pg) :
    pageReadable pg := by
  obtain ⟨hl, -, -, hk⟩ := treeWF_page _ _ _ pg h hpg
  refine ⟨hl, fun hf => ?_, fun hf => ?_⟩
  · rcases hk with ⟨-, hw, -⟩ | ⟨hb, -, -⟩
    · exact ⟨hw, fun i hi => (hg.1 hf i hi).1⟩
    · rw [hb] at hf; exact absurd hf (by unfold branchPageFlag leafPageFlag; decide)
  · rcases hk with ⟨hl', -, -⟩ | ⟨hb, hw, -⟩
    · exact absurd hl' hf
    · refine ⟨hw.2.2.1, fun i hi => ⟨(hw.2.2.2.1 i hi).1, (hw.2.2.2.1 i hi).2.1, hg.2 hb i hi⟩⟩

/-- What `b.node` needs to read the page of a page position (non-inline). -/
theorem nodeSrcOK_page (W : WView) (hwm : Nat) (B : BRec) (pm : GMap w64 Loc) (c : w64)
    (hv : viewOK W) (hpm : ∀ id, (W.pages !! uint.nat id).isSome → pm !! id = none)
    (hpage : B.bv.page' = null) (hroot : B.ib.root' ≠ W64 0) (hres : resolve B c = none)
    (hpos : posOK W hwm B c) :
    ∃ pg, W.pages !! uint.nat c = some pg ∧
      nodeSrcOK W B pm c (W.data +ₗ ((uint.nat c * W.ps : Nat) : Int)) pg Src.view := by
  obtain ⟨pg, hpg, -, hwf, -⟩ := posOK_page W hwm B c hroot hres hpos
  obtain ⟨hl, hid, -, hk⟩ := treeWF_page _ _ _ pg hwf hpg
  refine ⟨pg, hpg, pageReadable_of _ _ _ pg hwf hpg (hv.2.2.2.2.1 _ pg hpg),
    by simpa [Loc.add] using hv.1, fun h => absurd hpage h, fun _ => ⟨hpm c (by rw [hpg]; rfl),
    rfl, hpg, rfl, by rw [hid]; unfold uint.nat; word, validPageFlags_of pg (by
      rcases hk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]), hv.2.2.2.1 _ pg hpg⟩⟩

/-- A step down a path materializes the child (or finds it): the bucket stays clean, keeps
every position's kind and children, and the child is the node at its position. -/
theorem childStep (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (nk : Loc) (rk : NRec) (hrk : B.ns !! nk = some rk)
    (hbr : rk.nv.isLeaf' = false) (i : Nat) (w : WEntry) (hw : rk.ws[i]? = some w)
    (hnk : nk ≠ null) (p : Loc) (pg : List w8) (src : Src) (l : Loc) (B' : BRec)
    (st st' : go_etcd_io.bbolt.TxStats)
    (hsrc : B.nm !! w.pgid = none → W.pages !! uint.nat w.pgid = some pg ∧ src = Src.view)
    (hres : nodeRes B bl w.pgid nk p pg src l B' st st') :
    bktClean W hwm bl B' ∧ bktGrows B B' ∧ (∀ pid, kidsAt W B' pid = kidsAt W B pid) ∧
      resolve B' w.pgid = some l ∧ (B'.ns !! l).isSome := by
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 nk rk hrk; rw [hbr] at this; cases this
  rcases hres with ⟨hk, rfl, rfl⟩ | ⟨hk, hfresh, hl, -, s, cs', src', hs1, -, rfl⟩
  · refine ⟨hc, ⟨rfl, rfl, rfl, _, rfl⟩, fun _ => rfl, ?_, ?_⟩
    · unfold resolve; rw [if_neg hroot]; exact hk
    · obtain ⟨-, r, hr, -⟩ := hc.2.2.2.2.1 _ _ hk; rw [hr]; rfl
  · obtain ⟨hpg, rfl⟩ := hsrc hk
    have hsrc' := hs1 rfl
    subst hsrc'
    refine ⟨bktClean_addChild W hwm bl B hv hc nk rk i w hrk hbr hw hk l hfresh hl hnk pg hpg p s cs'
      Src.view (Or.inl rfl), ⟨rfl, rfl, rfl, B.bv.rootNode', by simp [nodeAdded, hnk]⟩,
      kidsAt_addChild W hwm bl B hc nk rk w.pgid hrk hbr hk l hfresh hnk pg hpg p s cs' Src.view, ?_, ?_⟩
    · unfold resolve
      rw [if_neg (show (nodeAdded B w.pgid nk l (readNRec bl nk p pg s Src.view) cs').ib.root' ≠ W64 0
        from hroot)]
      show (<[w.pgid := l]> B.nm) !! w.pgid = some l
      rw [GMap.lookup_insert]
    · rw [nodeAdded_ns B w.pgid nk l _ cs' rk hnk hrk, if_pos rfl]; rfl

theorem bktGrows_trans (B1 B2 B3 : BRec) (h1 : bktGrows B1 B2) (h2 : bktGrows B2 B3) :
    bktGrows B1 B3 := by
  obtain ⟨a1, b1, c1, r1, d1⟩ := h1
  obtain ⟨a2, b2, c2, r2, d2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, r2, ?_⟩
  rw [d2, d1]

theorem bktGrows_refl (B : BRec) : bktGrows B B := ⟨rfl, rfl, rfl, _, rfl⟩

theorem wpath_head (W : WView) (B : BRec) (pid : w64) (r : elemRef) (rs : List elemRef)
    (h : wpath W B pid (r :: rs)) : refAt W B pid r ∧ 0 ≤ sint.Z r.index' := by
  cases rs with
  | nil => exact ⟨h.1, h.2.1⟩
  | cons _ _ => exact ⟨h.1, h.2.1⟩

end steps

section nodepath
variable [ext : FfiSyntax]

/-- The page id `b.node` reads is the position's. -/
theorem nodeSrcOK_id (W : WView) (B : BRec) (pm : GMap w64 Loc) (pgid : w64) (p : Loc)
    (pg : List w8) (src : Src) (h : nodeSrcOK W B pm pgid p pg src) : W64 (pageId pg : Int) = pgid := by
  by_cases hp : B.bv.page' = null
  · exact (h.2.2.2 hp).2.2.2.2.1
  · obtain ⟨h0, -, -, -, -, hid⟩ := h.2.2.1 hp
    rw [h0, hid]; rfl

/-- What `b.node` needs to read the root's page (of a bucket with no node). -/
theorem rootSrcOK (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (pm : GMap w64 Loc)
    (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hpm : ∀ id, (W.pages !! uint.nat id).isSome → pm !! id = none)
    (hres : resolve B B.ib.root' = none) (p : Loc) (pg : List w8)
    (hpa : wpageAt W B B.ib.root' = some (p, pg)) (hcar : p.locCar ≠ 0) :
    nodeSrcOK W B pm B.ib.root' p pg (if B.bv.page' = null then Src.view else B.isrc) := by
  by_cases hr : B.ib.root' = W64 0
  · have hrn : B.bv.rootNode' = null := by
      unfold resolve at hres; rw [if_pos hr] at hres
      exact Classical.byContradiction fun h => by rw [if_neg h] at hres; cases hres
    obtain ⟨hpn, hsrc, hok⟩ := hc.1 hr hrn
    unfold wpageAt at hpa; rw [if_pos hr, if_pos hr] at hpa
    cases hpa
    obtain ⟨hid, hfl, hwf, hlen, hks⟩ := hok
    refine ⟨⟨hlen, fun _ => ⟨hwf, fun i hi => (hks i hi).1⟩, fun h => absurd hfl h⟩, hcar,
      fun _ => ⟨hr, rfl, rfl, by rw [if_neg hpn], by rw [if_neg hpn]; exact hsrc, hid⟩,
      fun h => absurd h hpn⟩
  · have hpn : B.bv.page' = null := hc.2.2.2.2.2.1 hr
    obtain ⟨pg', hpg', hok⟩ := nodeSrcOK_page W hwm B pm B.ib.root' hv hpm hpn hr hres
      (posOK_root W hwm bl B hc)
    unfold wpageAt at hpa; rw [if_neg hr, hpg'] at hpa
    cases hpa
    rw [if_pos hpn]; exact hok

/-- Materializing the root of a bucket with no node: the bucket stays clean, the root's node is
`l`, and a path from the root still selects the same children. -/
theorem rootStep (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (path : List elemRef) (hp : wpath W B B.ib.root' path)
    (hres0 : resolve B B.ib.root' = none) (p : Loc) (pg : List w8)
    (hpa : wpageAt W B B.ib.root' = some (p, pg)) (l : Loc) (B' : BRec)
    (st st' : go_etcd_io.bbolt.TxStats)
    (hres : nodeRes B bl B.ib.root' null p pg (if B.bv.page' = null then Src.view else B.isrc)
      l B' st st') :
    bktClean W hwm bl B' ∧ bktGrows B B' ∧ resolve B' B.ib.root' = some l ∧
      (B'.ns !! l).isSome ∧ kpath W B' B.ib.root' path := by
  have hrn : B.bv.rootNode' = null := Classical.byContradiction fun h => by
    unfold resolve at hres0
    split at hres0
    · first | cases hres0 | (rw [if_neg h] at hres0; cases hres0)
    · rw [hc.2.2.2.1 h] at hres0; cases hres0
  obtain ⟨hns0, hnm0⟩ := hc.2.2.1 hrn
  rcases hres with ⟨hk, -, -⟩ | ⟨-, -, hl, -, s, cs', src', hs1, hs2, rfl⟩
  · rw [hnm0] at hk; cases hk
  have hns' := nodeAdded_root_ns B B.ib.root' l (readNRec bl null p pg s src') cs' hns0
  have hnm' : (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').nm !! B.ib.root' =
      some l := by
    show (<[B.ib.root' := l]> B.nm) !! B.ib.root' = some l
    rw [GMap.lookup_insert]
  have hgrow : bktGrows B (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') :=
    ⟨rfl, rfl, rfl, l, by simp [nodeAdded]⟩
  have hsome : ((nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').ns !! l).isSome := by
    rw [hns', if_pos rfl]; rfl
  by_cases hr : B.ib.root' = W64 0
  · obtain ⟨hpn, hsrc, hok⟩ := hc.1 hr hrn
    have hpa' := hpa
    unfold wpageAt at hpa'; rw [if_pos hr, if_pos hr] at hpa'
    cases hpa'
    rw [if_neg hpn] at hs1 hs2
    have hsrc' : src' = Src.view ∨ src' = Src.own DFrac.discard := by
      by_cases h : B.isrc = Src.view
      · exact Or.inl (hs1 h)
      · exact Or.inr (hs2 h)
    refine ⟨bktClean_addRoot W hwm bl B hv hc hrn l hl B.ipg (fun h => absurd hr h) (fun _ => rfl)
      B.bv.page' s cs' src' hsrc', hgrow, ?_, hsome, ?_⟩
    · unfold resolve; simp [nodeAdded, hr, hl]
    · obtain ⟨r0, rest, rfl⟩ : ∃ r0 rest, path = r0 :: rest := by
        cases path with
        | nil => exact absurd hp (by simp [wpath])
        | cons a b => exact ⟨a, b, rfl⟩
      have hk0 : kidsAt W B B.ib.root' = some (true, []) := by
        unfold kidsAt; rw [hres0]; unfold wpageAt; rw [if_pos hr, if_pos hr]
        simp [hok.2.1]
      cases rest with
      | cons r2 rs =>
        obtain ⟨-, -, ks, c, hk, -⟩ := hp
        rw [hk0] at hk; cases hk
      | nil =>
        refine ⟨hp.2.1, [], ?_⟩
        unfold kidsAt
        have hrs : resolve (nodeAdded B B.ib.root' null l (readNRec bl null B.bv.page' B.ipg s src') cs')
            B.ib.root' = some l := by unfold resolve; simp [nodeAdded, hr, hl]
        rw [hrs]; dsimp only; rw [hns', if_pos rfl]
        simp [readNRec, readNodeV, hok.2.1]
  · have hpn : B.bv.page' = null := hc.2.2.2.2.2.1 hr
    rw [if_pos hpn] at hs1
    have hsv := hs1 rfl
    subst hsv
    have hpa' := hpa
    unfold wpageAt at hpa'; rw [if_neg hr] at hpa'
    obtain ⟨pg', hpg', heq⟩ := Option.map_eq_some_iff.1 hpa'
    cases heq
    refine ⟨bktClean_addRoot W hwm bl B hv hc hrn l hl pg (fun _ => hpg') (fun h => absurd h hr)
      _ s cs' Src.view (Or.inl rfl), hgrow, ?_, hsome, ?_⟩
    · unfold resolve; rw [if_neg (show (nodeAdded B B.ib.root' null l
        (readNRec bl null _ pg s Src.view) cs').ib.root' ≠ W64 0 from hr)]; exact hnm'
    · exact kpath_mono W B _ (kidsAt_addRoot W hwm bl B hc hrn hr l pg hpg' _ s cs' Src.view) _ _
        (kpath_of_wpath W B path _ hp)

/-- A step down a path from the node `nk` at position `pid`: a branch, and the child entry. -/
theorem pathStep (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (pm : GMap w64 Loc)
    (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hpm : ∀ id, (W.pages !! uint.nat id).isSome → pm !! id = none)
    (pid : w64) (nk : Loc) (rk : NRec) (hres : resolve B pid = some nk) (hrk : B.ns !! nk = some rk)
    (r r2 : elemRef) (rs : List elemRef) (hp : kpath W B pid (r :: r2 :: rs)) :
    rk.nv.isLeaf' = false ∧ 0 ≤ sint.Z r.index' ∧ ∃ w, rk.ws[(sint.Z r.index').toNat]? = some w ∧
      kpath W B w.pgid (r2 :: rs) ∧ (∀ l, B.nm !! w.pgid = some l → l ≠ null) ∧
      ∃ p pg, B.nm !! w.pgid = none → W.pages !! uint.nat w.pgid = some pg ∧
        nodeSrcOK W B pm w.pgid p pg Src.view := by
  obtain ⟨hi, ks, c, hk, hc', hrest⟩ := hp
  unfold kidsAt at hk; rw [hres] at hk; dsimp only at hk; rw [hrk] at hk
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨hleaf, rfl⟩ := hk
  simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.getElem?_map] at hc'
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hc'
  refine ⟨hleaf, hi, w, hw, hrest, fun l h => (hc.2.2.2.2.1 _ l h).1, ?_⟩
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 nk rk hrk; rw [hleaf] at this; cases this
  by_cases hn : B.nm !! w.pgid = none
  · obtain ⟨pg, hpg, hok⟩ := nodeSrcOK_page W hwm B pm w.pgid hv hpm (hc.2.2.2.2.2.1 hroot) hroot
      (by unfold resolve; rw [if_neg hroot]; exact hn)
      (posOK_node_child W hwm bl B nk rk hc hrk hleaf _ w hw)
    exact ⟨_, pg, fun _ => ⟨hpg, hok⟩⟩
  · exact ⟨null, [], fun h => absurd h hn⟩

/-- The end of a path: a leaf. -/
theorem pathEnd (W : WView) (B : BRec) (pid : w64) (nk : Loc) (rk : NRec)
    (hres : resolve B pid = some nk) (hrk : B.ns !! nk = some rk) (r : elemRef)
    (hp : kpath W B pid [r]) : rk.nv.isLeaf' = true := by
  obtain ⟨-, ks, hk⟩ := hp
  unfold kidsAt at hk; rw [hres] at hk; dsimp only at hk; rw [hrk] at hk
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
  exact hk.1

/-- A resolved position's node is not null. -/
theorem resolve_ne_null (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (pid : w64) (l : Loc) (h : resolve B pid = some l) : l ≠ null := by
  unfold resolve at h
  split at h
  · split at h
    · cases h
    · cases h; assumption
  · exact (hc.2.2.2.2.1 _ l h).1

/-- A resolved position's node has a record. -/
theorem resolve_ns (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (pid : w64) (l : Loc) (h : resolve B pid = some l) : ∃ r, B.ns !! l = some r := by
  unfold resolve at h
  split at h
  · split at h
    · cases h
    · cases h
      obtain ⟨-, r, hr, -⟩ := hc.2.2.2.2.1 _ _ (hc.2.2.2.1 ‹_›)
      exact ⟨r, hr⟩
  · obtain ⟨-, r, hr, -⟩ := hc.2.2.2.2.1 _ l h
    exact ⟨r, hr⟩

/-- The root's page of a bucket with no node: a header, and an inline page live. -/
theorem rootPage_facts (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hres : resolve B B.ib.root' = none) (p : Loc) (pg : List w8)
    (hpa : wpageAt W B B.ib.root' = some (p, pg)) :
    16 ≤ pg.length ∧ (B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale) := by
  by_cases hr : B.ib.root' = W64 0
  · have hrn : B.bv.rootNode' = null := by
      unfold resolve at hres; rw [if_pos hr] at hres
      exact Classical.byContradiction fun h => by rw [if_neg h] at hres; cases hres
    obtain ⟨hpn, hsrc, hok⟩ := hc.1 hr hrn
    unfold wpageAt at hpa; rw [if_pos hr, if_pos hr] at hpa
    cases hpa
    refine ⟨hok.2.2.2.1, fun _ => ⟨hpn, ?_⟩⟩
    rcases hsrc with h | h <;> rw [h] <;> nofun
  · obtain ⟨pg', hpg', hpa', hwf, -⟩ := posOK_page W hwm B B.ib.root' hr hres (posOK_root W hwm bl B hc)
    rw [hpa'] at hpa; cases hpa
    exact ⟨(treeWF_page _ _ _ _ hwf hpg').1, fun h => absurd h hr⟩

theorem drop_cons2 {α : Type} (l : List α) (n : Nat) (h : n + 1 < l.length) :
    ∃ a b rs, l.drop n = a :: b :: rs ∧ l.drop (n + 1) = b :: rs ∧ l[n]? = some a := by
  refine ⟨l[n], l[n+1], l.drop (n+2), ?_, ?_, List.getElem?_eq_getElem _⟩
  · rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  · rw [List.drop_eq_getElem_cons (by omega)]

theorem drop_last1 {α : Type} (l : List α) (n : Nat) (h : n + 1 = l.length) :
    ∃ a, l.drop n = [a] := by
  refine ⟨l[n], ?_⟩
  rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]

theorem bktGrows_tx (B B' : BRec) (h : bktGrows B B') : B'.bv.tx' = B.bv.tx' := by
  obtain ⟨-, -, -, rn, hbv⟩ := h
  rw [hbv]

end nodepath

end bbolt
end EtcdGrove
end Perennial
