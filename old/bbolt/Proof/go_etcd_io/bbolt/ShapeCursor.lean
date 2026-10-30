/-
`Cursor.node`'s shape (`Cursor.node.sspec`): the facts about a cursor's path that survive the
materialization of its positions (pure).

**Positions.** A materialization changes no position the bucket has (`bktExt`): its kind and
children (`kidsAt`), its keys (`keysAt`), and, a leaf, its entries' flags by key (`posKey`); so a
path's routing by a key (`kroute`) and its flags at the leaf (`pathKey`) carry over.

**Bounds.** The root node has no bounds (`bktKeysB`'s root clause), a child node has its entry's
(`nodeKeys`' parent clause), and a key routed at a branch is within its entry's bounds
(`keyIn_route`); so a key routed down a path from the root is within the bounds of the node at its
end (`wpath_bnd`, by induction along the path: below an unmaterialized page there is no node).
-/
module

public import Proof.go_etcd_io.bbolt.ShapeMat
public import Proof.go_etcd_io.bbolt.PathFlags

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section bnds
variable [ext : FfiSyntax]

theorem map_key_get (ws : List WEntry) (j : Nat) (h : j < ws.length) :
    (ws.map WEntry.key)[j]? = some (wKey ws j) := by
  unfold wKey
  rw [List.getElem?_map, List.getElem?_eq_getElem h]; rfl

/-- A key routed at entry `i` of a branch is within the entry's bounds. -/
theorem keyIn_route (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (i : Nat)
    (k : List w8) (hk : keyIn b.1 b.2 k) (hr : routes (ws.map WEntry.key) i k) :
    keyIn (entryBnd b ws i).1 (entryBnd b ws i).2 k := by
  obtain ⟨hlt, hlo, hhi⟩ := hr
  rw [List.length_map] at hlt
  refine ⟨?_, ?_⟩
  · show keyGe (childLo b.1 (wKey ws) i) k
    unfold childLo
    by_cases h0 : i = 0
    · rw [if_pos h0]; exact hk.1
    · rw [if_neg h0]
      intro l hl
      cases hl
      rcases hlo with h | ⟨ki, hki, hlt'⟩
      · exact absurd h h0
      · rw [map_key_get ws i hlt] at hki; cases hki; exact hlt'
  · show keyLt k (childHi b.2 (wKey ws) ws.length i)
    unfold childHi
    by_cases h1 : i + 1 < ws.length
    · rw [if_pos h1]
      intro h hh
      cases hh
      exact hhi _ (map_key_get ws (i + 1) h1)
    · rw [if_neg h1]; exact hk.2

/-- A materialized child's bounds are its entry's. -/
theorem bnd_child (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB W B bnd) (nk : Loc) (rk : NRec)
    (hrk : B.ns !! nk = some rk) (hbr : rk.nv.isLeaf' = false) (i : Nat) (w : WEntry)
    (hw : rk.ws[i]? = some w) (l : Loc) (hl : B.nm !! w.pgid = some l) :
    bnd l = entryBnd (bnd nk) rk.ws i := by
  have hN := hc.2.2.2.2.2.2.2.1 nk rk hrk
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -, h12, -⟩ := hN
  obtain ⟨-, hnd, hkids⟩ := h12 hbr
  obtain ⟨-, hsome, -⟩ := hkids w (List.mem_of_getElem? hw)
  obtain ⟨r', hr', hpar⟩ := hsome l hl
  have hnk : nk ≠ null := (hc.2.2.2.2.1 _ _ h7).1
  obtain ⟨-, r'', hr'', hpg''⟩ := hc.2.2.2.2.1 _ _ hl
  rw [hr'] at hr''; cases hr''
  obtain ⟨-, -, c3, -⟩ := hk.2.2 l r' hr'
  obtain ⟨-, rp, i', w', hrp, hw', hpg', -, hbnd⟩ := c3 (by rw [hpar]; exact hnk)
  rw [hpar, hrk] at hrp; cases hrp
  rw [hpar] at hbnd
  have hii : i' = i := by
    refine Classical.byContradiction fun hne => ?_
    exact nodup_pgid_ne rk.ws hnd i i' w w' hw hw' hne (by rw [hpg', hpg''])
  rw [hii] at hbnd; exact hbnd

/-- The root node has no bounds. -/
theorem bnd_root (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : bktKeysB W B bnd) (r : NRec) (hr : B.ns !! B.bv.rootNode' = some r) :
    bnd B.bv.rootNode' = (none, none) :=
  (hk.2.2 _ r hr).2.1 (hk.2.1 r hr)

/-- The node at the root position is the root node. -/
theorem resolve_root (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (l : Loc) (h : resolve B B.ib.root' = some l) : l = B.bv.rootNode' := by
  unfold resolve at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · by_cases hrn : B.bv.rootNode' = null
    · rw [(hc.2.2.1 hrn).2] at h; cases h
    · rw [hc.2.2.2.1 hrn] at h; cases h; rfl

/-- A key routed down a stack from a position whose node (if any) has it within its bounds is
within the bounds of the node at the end (if any). -/
theorem wpath_bnd (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB W B bnd) (k : List w8) :
    ∀ (es : List elemRef) (pid : w64), wpath W B pid es → kroute W B k pid es → posOK W hwm B pid →
      (∀ nk, resolve B pid = some nk → keyIn (bnd nk).1 (bnd nk).2 k) →
      ∀ rt, es.getLast? = some rt → rt.node' ≠ null → keyIn (bnd rt.node').1 (bnd rt.node').2 k := by
  intro es
  induction es with
  | nil => intro pid h; exact absurd h (by simp [wpath])
  | cons r rs ih =>
    intro pid h hkr hpos hbnd rt hlast hn
    cases rs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      rcases h.1 with ⟨l, h1, h2, -⟩ | ⟨-, h2, -⟩
      · rw [h2]; exact hbnd l h1
      · exact absurd h2 hn
    | cons r2 rs' =>
      obtain ⟨hr, hi, ks, c, hkd, hc', hrest⟩ := h
      obtain ⟨kss, cs, c', hks, hrt, hkd', hc'', hkr'⟩ := hkr
      rw [hkd] at hkd'; cases hkd'
      rw [hc'] at hc''; cases hc''
      have hl' : (r2 :: rs').getLast? = some rt := by simpa using hlast
      unfold kidsAt at hkd
      rcases hpos.2 with ⟨l, rr, hres, hrr⟩ | ⟨hres, hpg⟩
      · rw [hres] at hkd
        simp only [hrr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkd
        obtain ⟨hleaf, rfl⟩ := hkd
        simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.getElem?_map] at hc'
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hc'
        have hroot : B.ib.root' ≠ W64 0 := by
          intro h0; have := hc.2.2.2.2.2.2.1 h0 l rr hrr; rw [hleaf] at this; cases this
        refine ih w.pgid hrest hkr' (posOK_node_child W hwm bl B l rr hc hrr hleaf _ w hw) ?_ rt hl' hn
        intro nk hnk
        unfold resolve at hnk; rw [if_neg hroot] at hnk
        rw [bnd_child W hwm bl B hc bnd hk l rr hrr hleaf _ w hw nk hnk]
        unfold keysAt at hks; rw [hres] at hks
        simp only [hrr, Option.map_some, Option.some.injEq] at hks
        subst hks
        exact keyIn_route _ rr.ws _ k (hbnd l hres) hrt
      · rw [hres] at hkd
        rcases hpg with ⟨h0, -, -, -, hinl⟩ | ⟨hr0, hwf, hfree⟩
        · have hp0 := hpos.1 h0
          simp only [wpageAt, h0, hp0, ↓reduceIte, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hkd
          obtain ⟨hleaf, -⟩ := hkd
          exfalso; revert hleaf; simp [hinl.2.1]
        · obtain ⟨pg, hpg, hpa, -, -⟩ := posOK_page W hwm B pid hr0 hres hpos
          simp only [hpa, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkd
          obtain ⟨hleaf, rfl⟩ := hkd
          obtain ⟨-, -, -, hkind⟩ := treeWF_page _ _ _ pg hwf hpg
          rcases hkind with ⟨hfl, -⟩ | ⟨hfl, -, hkids⟩
          · exfalso; revert hleaf; simp [hfl]
          · rw [if_neg (by rw [hfl]; unfold branchPageFlag leafPageFlag; decide),
              List.getElem?_map] at hc'
            obtain ⟨i, hi', rfl⟩ := Option.map_eq_some_iff.1 hc'
            have hil := (List.mem_range.1 (List.mem_of_getElem? hi'))
            refine ih _ hrest hkr' (posOK_page_child W hwm B pid pg hr0 hpg hfl hkids hfree _ hil) ?_ rt hl' hn
            intro nk hnk
            exfalso
            unfold resolve at hnk; rw [if_neg hr0] at hnk
            cases hkids i hil with
            | page _ cpg _ hcpg _ _ =>
              rw [hfree _ (treeHas_child _ _ pg hpg hfl i hil _ (treeHas_self _ _ cpg hcpg))] at hnk
              cases hnk

/-- The flags at the end of a stack, if it ends at a node. -/
theorem wpath_pathKey (W : WView) (B : BRec) (k : List w8) (P : w32 → Prop) :
    ∀ (es : List elemRef) (pid : w64), wpath W B pid es → pathKey W B k P pid es →
      ∀ rt, es.getLast? = some rt → rt.node' ≠ null → ∀ r, B.ns !! rt.node' = some r →
        ∀ w ∈ r.ws, w.key = k → P w.flags := by
  intro es
  induction es with
  | nil => intro pid h; exact absurd h (by simp [wpath])
  | cons r rs ih =>
    intro pid h hpk rt hlast hn
    cases rs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      rcases h.1 with ⟨l, h1, h2, -⟩ | ⟨-, h2, -⟩
      · rw [h2]; exact fun r hr => hpk.1 l r h1 hr
      · exact absurd h2 hn
    | cons r2 rs' =>
      obtain ⟨-, -, ks, c, hkd, hc', hrest⟩ := h
      obtain ⟨cs, c', hkd', hc'', hpk'⟩ := hpk
      rw [hkd] at hkd'; cases hkd'
      rw [hc'] at hc''; cases hc''
      exact ih c hrest hpk' rt (by simpa using hlast) hn

end bnds

/-! ### Positions kept by a materialization -/

section ext
variable [ext : FfiSyntax]

/-- Every position of `B` is one of `B'`, with its kind, children, keys and (a leaf) flags by key. -/
def bktExt (W : WView) (B B' : BRec) : Prop :=
  ∀ pid, (kidsAt W B pid).isSome → kidsAt W B' pid = kidsAt W B pid ∧ keysAt W B' pid = keysAt W B pid ∧
    ∀ ks, kidsAt W B pid = some (true, ks) → ∀ k P, posKey W B pid k P → posKey W B' pid k P

theorem bktExt_refl (W : WView) (B : BRec) : bktExt W B B :=
  fun _ _ => ⟨rfl, rfl, fun _ _ _ _ h => h⟩

theorem bktExt_trans (W : WView) (B1 B2 B3 : BRec) (h1 : bktExt W B1 B2) (h2 : bktExt W B2 B3) :
    bktExt W B1 B3 := by
  intro pid hs
  obtain ⟨a1, b1, c1⟩ := h1 pid hs
  obtain ⟨a2, b2, c2⟩ := h2 pid (by rw [a1]; exact hs)
  exact ⟨a2.trans a1, b2.trans b1, fun ks hks k P hp =>
    c2 ks (by rw [a1]; exact hks) k P (c1 ks hks k P hp)⟩

theorem kroute_ext (W : WView) (B B' : BRec) (h : bktExt W B B') (k : List w8) :
    ∀ (es : List elemRef) (pid : w64), kroute W B k pid es → kroute W B' k pid es := by
  intro es
  induction es with
  | nil => intro pid h; exact h
  | cons r rs ih =>
    intro pid hp
    cases rs with
    | nil => trivial
    | cons r2 rs' =>
      obtain ⟨ks, cs, c, hks, hr, hkd, hc, hrest⟩ := hp
      obtain ⟨a, b, -⟩ := h pid (by rw [hkd]; rfl)
      exact ⟨ks, cs, c, by rw [b]; exact hks, hr, by rw [a]; exact hkd, hc, ih c hrest⟩

theorem pathKey_ext (W : WView) (B B' : BRec) (h : bktExt W B B') (k : List w8) (P : w32 → Prop) :
    ∀ (es : List elemRef) (pid : w64), kpath W B pid es → pathKey W B k P pid es →
      pathKey W B' k P pid es := by
  intro es
  induction es with
  | nil => intro pid h; exact absurd h (by simp [kpath])
  | cons r rs ih =>
    intro pid hkp hp
    cases rs with
    | nil =>
      obtain ⟨-, ks, hks⟩ := hkp
      exact (h pid (by rw [hks]; rfl)).2.2 ks hks k P hp
    | cons r2 rs' =>
      obtain ⟨-, ks, c, hkd, hc, hrest⟩ := hkp
      obtain ⟨cs, c', hkd', hc', hp'⟩ := hp
      rw [hkd] at hkd'; cases hkd'
      rw [hc] at hc'; cases hc'
      obtain ⟨a, -, -⟩ := h pid (by rw [hkd]; rfl)
      exact ⟨_, _, by rw [a]; exact hkd, hc, ih c hrest hp'⟩

/-- A position materialized from its page. -/
theorem pos_mat (W : WView) (B B' : BRec) (pid : w64) (l : Loc) (r : NRec) (pg : List w8)
    (src : Src) (p0 : Loc) (hres : resolve B pid = none) (hpa : wpageAt W B pid = some (p0, pg))
    (hres' : resolve B' pid = some l) (hr : B'.ns !! l = some r) (hws : r.ws = pageWs pg src)
    (hleaf : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag)) :
    kidsAt W B' pid = kidsAt W B pid ∧ keysAt W B' pid = keysAt W B pid ∧
      ∀ ks, kidsAt W B pid = some (true, ks) → ∀ k P, posKey W B pid k P → posKey W B' pid k P := by
  refine ⟨?_, ?_, ?_⟩
  · unfold kidsAt; rw [hres, hres', hpa]
    simp only [hr, Option.map_some, hleaf, hws]
    by_cases hf : pageFlags pg = leafPageFlag
    · simp [hf]
    · simp [hf, pageWs_pgids pg src hf]
  · unfold keysAt; rw [hres, hres', hpa]
    simp only [hr, Option.map_some, hws]
    unfold pageWs; rw [List.map_map]
    congr 2; funext j; exact pageW_key_pageKey pg src j
  · intro ks hks k P hp
    unfold kidsAt at hks; rw [hres, hpa] at hks
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hks
    have hl := hks.1
    refine ⟨fun l1 r1 h1 h2 w hw hk => ?_, fun h => by rw [hres'] at h; cases h⟩
    rw [hres'] at h1; cases h1
    rw [hr] at h2; cases h2
    rw [hws] at hw
    obtain ⟨i, hi, rfl⟩ := pageWs_mem pg src w hw
    obtain ⟨hk1, -, hf1⟩ := pageW_leaf pg src i hl
    rw [hf1]
    exact hp.2 hres _ hpa i hi (by rw [← hk1]; exact hk)

/-- A position a materialization did not touch. -/
theorem pos_same (W : WView) (B B' : BRec) (pid : w64) (hres : resolve B' pid = resolve B pid)
    (hpa : wpageAt W B' pid = wpageAt W B pid)
    (hsome : ∀ l, resolve B pid = some l → (B.ns !! l).isSome)
    (hns : ∀ l r, resolve B pid = some l → B.ns !! l = some r → ∃ r', B'.ns !! l = some r' ∧
      r'.ws = r.ws ∧ r'.nv.isLeaf' = r.nv.isLeaf') :
    kidsAt W B' pid = kidsAt W B pid ∧ keysAt W B' pid = keysAt W B pid ∧
      ∀ ks, kidsAt W B pid = some (true, ks) → ∀ k P, posKey W B pid k P → posKey W B' pid k P := by
  cases hr : resolve B pid with
  | none =>
    refine ⟨by unfold kidsAt; rw [hres, hr, hpa], by unfold keysAt; rw [hres, hr, hpa], ?_⟩
    intro ks _ k P hp
    refine ⟨fun l1 r1 h1 => (by rw [hres, hr] at h1; cases h1), fun h lp hlp => ?_⟩
    rw [hpa] at hlp; exact hp.2 hr lp hlp
  | some l =>
    obtain ⟨rB, hrB⟩ := Option.isSome_iff_exists.1 (hsome l hr)
    obtain ⟨r', hr', hws, hlf⟩ := hns l rB hr hrB
    refine ⟨?_, ?_, ?_⟩
    · unfold kidsAt; rw [hres, hr]; simp only [hr', hrB, Option.map_some, hws, hlf]
    · unfold keysAt; rw [hres, hr]; simp only [hr', hrB, Option.map_some, hws]
    · intro ks _ k P hp
      refine ⟨fun l1 r1 h1 h2 w hw hk => ?_, fun h => by rw [hres, hr] at h; cases h⟩
      rw [hres, hr] at h1; cases h1
      rw [hr'] at h2; cases h2
      rw [hws] at hw
      exact hp.1 l rB hr hrB w hw hk

/-- Materializing a child keeps the positions. -/
theorem ext_addChild (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (c : w64)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hnone : B.nm !! c = none) (l : Loc) (hfresh : B.ns !! l = none)
    (hnl : nl ≠ null) (pg : List w8) (hpg : W.pages !! uint.nat c = some pg) (p : Loc)
    (s cs' : GoSlice) (src' : Src) :
    bktExt W B (nodeAdded B c nl l (readNRec bl nl p pg s src') cs') := by
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 nl rp hrp; rw [hbr] at this; cases this
  have hres : ∀ B0 : BRec, B0.ib.root' ≠ W64 0 → ∀ pid, resolve B0 pid = B0.nm !! pid := by
    intro B0 h pid; unfold resolve; rw [if_neg h]
  have hbv' : (nodeAdded B c nl l (readNRec bl nl p pg s src') cs').bv = B.bv := by
    simp [nodeAdded, hnl]
  have hpa : ∀ pid, wpageAt W (nodeAdded B c nl l (readNRec bl nl p pg s src') cs') pid = wpageAt W B pid := by
    intro pid; unfold wpageAt; rw [hbv']; rfl
  have hns' := nodeAdded_ns B c nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  intro pid _
  by_cases hpc : pid = c
  · subst hpc
    refine pos_mat W B _ pid l _ pg src' (W.data +ₗ ((uint.nat pid * W.ps : Nat) : Int))
      (by rw [hres B hroot]; exact hnone) ?_
      (by rw [hres (nodeAdded B pid nl l (readNRec bl nl p pg s src') cs') hroot]
          show (<[pid := l]> B.nm) !! pid = some l; rw [GMap.lookup_insert])
      (by rw [hns', if_pos rfl]) rfl rfl
    unfold wpageAt; rw [if_neg hroot, hpg]; rfl
  · refine pos_same W B _ pid (by
        rw [hres (nodeAdded B c nl l (readNRec bl nl p pg s src') cs') hroot, hres B hroot]
        show (<[c := l]> B.nm) !! pid = _
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hpc)]) (hpa pid)
      (fun l' h => by obtain ⟨r, h1⟩ := resolve_ns W hwm bl B hc pid l' h; rw [h1]; rfl) ?_
    intro l' r' _ h'
    obtain ⟨ry', a, b, c', -⟩ := ns_addChild B c nl l (readNRec bl nl p pg s src') cs' rp hnl hrp hfresh l' r' h'
    exact ⟨ry', a, b, c'⟩

/-- Materializing the root keeps the positions. -/
theorem ext_addRoot (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (l : Loc) (hl : l ≠ null)
    (pg : List w8)
    (hpgf : B.ib.root' ≠ W64 0 → W.pages !! uint.nat B.ib.root' = some pg)
    (hpgi : B.ib.root' = W64 0 → pg = B.ipg) (p : Loc) (s cs' : GoSlice) (src' : Src) :
    bktExt W B (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') := by
  obtain ⟨hns0, hnm0⟩ := hc.2.2.1 hrn
  have hns' := nodeAdded_root_ns B B.ib.root' l (readNRec bl null p pg s src') cs' hns0
  have hpa : ∀ pid, wpageAt W (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') pid =
      wpageAt W B pid := by
    intro pid; unfold wpageAt; simp [nodeAdded]
  intro pid hs
  by_cases hr : B.ib.root' = W64 0
  · have hres0 : resolve B pid = none := by unfold resolve; rw [if_pos hr, if_pos hrn]
    have hres1 : resolve (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') pid = some l := by
      unfold resolve; simp [nodeAdded, hr, hl]
    have hp0 : pid = W64 0 := by
      unfold kidsAt at hs; rw [hres0] at hs
      unfold wpageAt at hs; rw [if_pos hr] at hs
      refine Classical.byContradiction fun h => ?_
      rw [if_neg h] at hs; cases hs
    subst hp0
    refine pos_mat W B _ (W64 0) l _ pg src' B.bv.page' hres0 ?_ hres1 (by rw [hns', if_pos rfl]) rfl rfl
    unfold wpageAt; rw [if_pos hr, if_pos rfl, hpgi hr]
  · have hres : ∀ B0 : BRec, B0.ib.root' ≠ W64 0 → ∀ pid, resolve B0 pid = B0.nm !! pid := by
      intro B0 h pid; unfold resolve; rw [if_neg h]
    by_cases hpc : pid = B.ib.root'
    · subst hpc
      refine pos_mat W B _ _ l _ pg src' (W.data +ₗ ((uint.nat B.ib.root' * W.ps : Nat) : Int))
        (by rw [hres B hr, hnm0]; rfl) ?_
        (by rw [hres (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') hr]
            show (<[B.ib.root' := l]> B.nm) !! B.ib.root' = some l; rw [GMap.lookup_insert])
        (by rw [hns', if_pos rfl]) rfl rfl
      unfold wpageAt; rw [if_neg hr, hpgf hr]; rfl
    · refine pos_same W B _ pid (by
          rw [hres (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') hr, hres B hr]
          show (<[B.ib.root' := l]> B.nm) !! pid = _
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hpc)]) (hpa pid)
        (fun l' h => by rw [hres B hr, hnm0] at h; cases h) (fun l' r' h => by
          rw [hres B hr, hnm0] at h; cases h)

/-- `Bucket.node`'s result keeps the positions (a child, as `childStep`). -/
theorem ext_childRes (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (nk : Loc) (rk : NRec) (hrk : B.ns !! nk = some rk)
    (hbr : rk.nv.isLeaf' = false) (w : WEntry) (hnk : nk ≠ null) (p : Loc) (pg : List w8)
    (src : Src) (l : Loc) (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats)
    (hsrc : B.nm !! w.pgid = none → W.pages !! uint.nat w.pgid = some pg)
    (hres : nodeRes B bl w.pgid nk p pg src l B' st st') : bktExt W B B' := by
  rcases hres with ⟨-, hB, -⟩ | ⟨hk, hfresh, -, -, s, cs', src', -, -, rfl⟩
  · rw [hB]; exact bktExt_refl W B
  · exact ext_addChild W hwm bl B hc nk rk w.pgid hrk hbr hk l hfresh hnk pg (hsrc hk) p s cs' src'

/-- `Bucket.node`'s result keeps the positions (the root, as `rootStep`). -/
theorem ext_rootRes (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (hres0 : resolve B B.ib.root' = none) (p : Loc) (pg : List w8)
    (hpa : wpageAt W B B.ib.root' = some (p, pg)) (l : Loc) (B' : BRec)
    (st st' : go_etcd_io.bbolt.TxStats) (src : Src)
    (hres : nodeRes B bl B.ib.root' null p pg src l B' st st') : bktExt W B B' := by
  have hrn : B.bv.rootNode' = null := Classical.byContradiction fun h => by
    unfold resolve at hres0
    split at hres0
    · first | cases hres0 | (rw [if_neg h] at hres0; cases hres0)
    · rw [hc.2.2.2.1 h] at hres0; cases hres0
  rcases hres with ⟨-, hB, -⟩ | ⟨-, -, hl, -, s, cs', src', -, -, rfl⟩
  · rw [hB]; exact bktExt_refl W B
  · refine ext_addRoot W hwm bl B hc hrn l hl pg (fun hr => ?_) (fun hr => ?_) p s cs' src'
    · unfold wpageAt at hpa; rw [if_neg hr] at hpa
      obtain ⟨pg', hpg', heq⟩ := Option.map_eq_some_iff.1 hpa
      cases heq; exact hpg'
    · unfold wpageAt at hpa; rw [if_pos hr, if_pos hr] at hpa
      cases hpa; rfl

end ext

section more
variable [ext : FfiSyntax]

/-- A bucket whose root position has no node has no root node. -/
theorem rootNode_null (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (h : resolve B B.ib.root' = none) : B.bv.rootNode' = null := Classical.byContradiction fun hn => by
  unfold resolve at h
  split at h
  · first | cases h | (rw [if_neg hn] at h; cases h)
  · rw [hc.2.2.2.1 hn] at h; cases h

/-- `Bucket.node`'s result keeps the old nodes' entries and kinds. -/
theorem ns_childRes (B : BRec) (bl : Loc) (c : w64) (nk p : Loc) (pg : List w8) (src : Src) (l : Loc)
    (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats) (rk : NRec) (hnk : nk ≠ null)
    (hrk : B.ns !! nk = some rk) (hres : nodeRes B bl c nk p pg src l B' st st') :
    ∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧ ry'.ws = ry.ws ∧
      ry'.nv.isLeaf' = ry.nv.isLeaf' := by
  intro y ry hy
  rcases hres with ⟨-, hB, -⟩ | ⟨-, hfresh, -, -, s, cs', src', -, -, hB⟩
  · rw [hB]; exact ⟨ry, hy, rfl, rfl⟩
  · rw [hB]
    obtain ⟨ry', a, b, c', -⟩ := ns_addChild B c nk l _ cs' rk hnk hrk hfresh y ry hy
    exact ⟨ry', a, b, c'⟩

end more

section shape
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

open Iris.ProofMode in
theorem bktShape_keys (γ : GName) (W : WView) (B : BRec) :
    bktShape (GF := GF) γ W B ⊢ bktShape γ W B ∗ ⌜bktKeys W B⌝ := by
  unfold bktShape
  iintro ⟨Ht, %Hk⟩
  isplitl [Ht]
  · iframe; ipureintro; exact Hk
  · ipureintro; exact Hk

end shape

end bbolt
end EtcdGrove
end Perennial
