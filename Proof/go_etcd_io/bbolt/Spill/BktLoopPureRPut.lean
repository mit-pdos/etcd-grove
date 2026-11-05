/-
`Bucket.spill`'s root loop (U9x2, `notes/bbolt-proof-plan.md`): **the staged value put into the
root bucket's leaf** (`rinv_put'`, `BktLoopStep.rinv_put`'s proof). After `Cursor.node`'s
materializations (`matGrow`: the root bucket searchable, its logical tree by data, the other
buckets and the writer's global fields kept) the search's leaf `l` holds the child's bucket entry
(the route's block is the only one holding its key); `node.put` replaces it (`wsPutAt` at a found
key), which keeps the root bucket searchable (`bktLocalOK_putOpened`), its finite tree
(`ltIs_leafRep`), the spill's global state (`spG_setNode`), the children (their buckets untouched,
`childSt_kept`), and replaces the child's value in the root entries (`rootEnts_putAt`).

The root bucket's nodes' shape (`rootLoc`'s node clause) for the nodes `Cursor.node` reads from
view pages is `rootPage_shape` (U9x3: from `RInv.rootPos` and `RInv.shape0`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureRPutT
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureSpilled
public import Proof.go_etcd_io.bbolt.Read.LRoutes
public import Proof.go_etcd_io.bbolt.Read.LeafFor
public import Proof.go_etcd_io.bbolt.Write.CurNode
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsLeaf
public import Proof.go_etcd_io.bbolt.Spill.BktLoopExtMat

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section rput
variable [GooseExts]

/-- The root entry the loop puts for child `k` with the value `v` (the value persistent). -/
def rootEnt (k v : List w8) : WEntry := ⟨W32 1, W64 0, k, v, Src.heap, Src.heap⟩

/-- `rootLoc`'s node clause: a bucket's nodes non-empty below the root, its branches of two
entries, its entries' keys non-empty and within `bboltEntryMax`. -/
def rootNodesOK (B : BRec) : Prop :=
  ∀ l r, B.ns !! l = some r →
    ((r.nv.parent' ≠ null → 0 < r.ws.length) ∧ (r.nv.isLeaf' = false → 2 ≤ r.ws.length)) ∧
    ∀ w ∈ r.ws, 0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax

variable {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString} {Lroot : List Nat}
  {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}

theorem setNode_tt (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.t = X.t.t := by
  unfold WX.setNode; split <;> rfl

/-- **Materializations keep the transaction's struct.** -/
theorem matGrow_tt {X Y : WX} {bl : Loc} (h : matGrow X Y bl) : Y.t.t = X.t.t := by
  induction h with
  | refl => rfl
  | step X Y Z bl l pgid parent hadd _ _ ih =>
    obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hX'⟩ := hadd
    subst hX'; exact ih

/-- **Materializations keep `rootUnder`** (`rootUnder_nodeAdded` at each step). -/
theorem rootUnder_matGrow {X Y : WX} {bl : Loc} {B0 : BRec} {P : Pages} (h : matGrow X Y bl) :
    bktLocalOK X bl → (∀ B, X.t.bs !! bl = some B → B.ib.root' ≠ W64 0) → X.v.pages = P →
    (∀ B, X.t.bs !! bl = some B → rootUnder P B0 B) →
    ∀ B, Y.t.bs !! bl = some B → rootUnder P B0 B := by
  induction h with
  | refl => intro _ _ _ hU; exact hU
  | step X Y Z bl l pgid parent hadd hpos hm ih =>
    intro hbl h0 hP hU
    obtain ⟨hblY, hvY, -, hibY, -⟩ :=
      matGrow_keep (matGrow.step X Y Y bl l pgid parent hadd hpos (matGrow.refl Y bl)) hbl h0
    have hUY : ∀ B, Y.t.bs !! bl = some B → rootUnder Y.v.pages B0 B := by
      refine rootUnder_nodeAdded (hwm := X.t.mv.pgid'.toNat) hadd hpos ?_
      intro B hB
      obtain ⟨-, B', hB', hcl, -⟩ := hbl
      rw [hB] at hB'; cases hB'
      exact ⟨hcl, h0 B hB, by rw [hP]; exact hU B hB⟩
    apply ih hblY
    · intro B hB
      obtain ⟨Bx, hBx⟩ := Option.isSome_iff_exists.1 (show (X.t.bs !! bl).isSome by
        obtain ⟨-, B, hB, -⟩ := hbl; rw [hB]; rfl)
      obtain ⟨B', hB', hib⟩ := hibY Bx hBx
      rw [hB] at hB'; cases hB'
      rw [hib]; exact h0 Bx hBx
    · rw [hvY]; exact hP
    · intro B hB; have := hUY B hB; rw [hvY, hP] at this; exact this

theorem pageW_value_branch (pg : List w8) (j : Nat) (hl : pageFlags pg ≠ leafPageFlag) :
    (pageW pg j).value = [] := by
  unfold pageW; rw [if_neg hl]

/-- **The shape of a root bucket's view page `Cursor.node` reads.** The page is under a position
of the root bucket at the start (`RInv.rootPos`, `rootUnder_matGrow`), so its leaf entries are
bounded (`RInv.shape0`) and its branch keys too (exact branch keys, `treeKeys_keyLe`); a branch
page has two entries and a child page one (`bktKeys`' `treeKeys`). -/
theorem rootPage_shape (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {Y Y' : WX} {l : Loc}
    {pgid : w64} {parent : Loc} (hY : matGrow X Y X0.rl)
    (hadd : nodeAdded Y Y' X0.rl l pgid parent) (hpos : matPos Y X0.rl pgid parent) :
    ∀ B pa pg, Y.t.bs !! X0.rl = some B → wpageAt Y.v B pgid = some (pa, pg) →
      (parent ≠ null → 0 < pageCount pg) ∧ (pageFlags pg ≠ leafPageFlag → 2 ≤ pageCount pg) ∧
      ∀ i < pageCount pg, 0 < (pageW pg i).key.length ∧
        (pageW pg i).key.length + (pageW pg i).value.length ≤ bboltEntryMax := by
  have h0 : ∀ B, X.t.bs !! X0.rl = some B → B.ib.root' ≠ W64 0 := by
    intro B hB; rw [hI.rootIb B hB]; exact hI.rootPg
  obtain ⟨hlocY, hvY, -, hibY, -⟩ := matGrow_keep hY hI.rootOK.1 h0
  have hUY := rootUnder_matGrow hY hI.rootOK.1 h0 hI.pages hI.rootPos
  intro B pa pg hB hwp
  have h0B : B.ib.root' ≠ W64 0 := by
    obtain ⟨Bx, hBx, -⟩ := hI.root
    obtain ⟨B', hB', hib⟩ := hibY Bx hBx
    rw [hB] at hB'; cases hB'
    rw [hib]; exact h0 Bx hBx
  obtain ⟨-, B', hB', hcl, ⟨bnd, hbk⟩, -, -, hvw⟩ := hlocY
  rw [hB] at hB'; cases hB'
  have hpp := matPos_posRoot hpos hB h0B
  have hpg := wpageAt_page h0B hwp
  obtain ⟨c0, hc0, hto⟩ := hUY B hB _ hpp
  have hPY : Y.v.pages = X0.v.pages := by rw [hvY, hI.pages]
  have hpg0 : X0.v.pages !! pgid.toNat = some pg := by rw [← hPY]; exact hpg
  have hown := ownTo_ownHas hto hpg0
  obtain ⟨lo, hi', htk, hcnt⟩ : ∃ lo hi, treeKeys Y.v.pages pgid.toNat lo hi ∧
      (parent ≠ null → 0 < pageCount pg) := by
    obtain ⟨B1, hB1, hp⟩ := hpos
    rw [hB] at hB1; cases hB1
    rcases hp with ⟨hpar, hrn, rfl⟩ | ⟨i, r, w, hr, hlf, hw, hwp', hnm⟩
    · exact ⟨none, none, hbk.1 hrn h0B, fun h => absurd hpar h⟩
    · obtain ⟨-, -, -, hk3, -, -⟩ := hbk.2.2 parent r hr
      obtain ⟨-, kind, hkd⟩ := hk3 hlf
      obtain ⟨pg', hpg', hc, -, -, htk⟩ := (hkd i w hw).2 (by rw [hwp']; exact hnm)
      rw [hwp', hpg] at hpg'; cases hpg'
      exact ⟨_, _, by rw [← hwp']; exact htk, fun _ => hc⟩
  have hpt : pageTreeWF Y.v.pages Y.t.mv.pgid'.toNat pg pg.length := by
    rcases posRoot_treeWF hcl hpp with ⟨_, pg', _, _, hpg', _, _, hpt⟩
    rw [hpg] at hpg'; cases hpg'; exact hpt
  have hkpos := Write.pageKeys_pos _ _ pg hpt ((mat_strict Y.v hvw).1 _ pg hpg)
  have hL : ∀ q qpg, ownHas X0.v.pages c0 q → X0.v.pages !! q = some qpg →
      pageFlags qpg = leafPageFlag → ∀ i < pageCount qpg, leafKsize qpg i ≤ maxKeySize :=
    fun q qpg h1 h2 h3 i hi => (hI.shape0 c0 q qpg hc0 h1 h2 h3 i hi).2.2
  refine ⟨hcnt, fun hnl => ?_, fun i hi => ⟨by rw [mat_pageW_key]; exact hkpos i hi, ?_⟩⟩
  · cases htk with
    | leaf _ pg' _ _ hp' hf _ _ => rw [hpg] at hp'; cases hp'; exact absurd hf hnl
    | branch _ pg' _ _ _ hp' _ h2 _ _ _ => rw [hpg] at hp'; cases hp'; exact h2
  · by_cases hfl : pageFlags pg = leafPageFlag
    · obtain ⟨-, -, f3, f4⟩ := mat_pageW_leaf pg i hfl
      have hs := hI.shape0 c0 _ pg hc0 hown hpg0 hfl i hi
      rw [f3, f4]
      unfold leafKey leafValue
      have := Write.bytesAt_length_le pg (elemOff i + leafPos pg i) (leafKsize pg i)
      have := Write.bytesAt_length_le pg (elemOff i + leafPos pg i + leafKsize pg i)
        (leafVsize pg i)
      omega
    · rw [pageW_value_branch pg i hfl, mat_pageW_key]
      have htk0 : treeKeys X0.v.pages pgid.toNat lo hi' := by rw [← hPY]; exact htk
      have := treeKeys_keyLe htk0 hown hL pg hpg0 i hi
      simp only [List.length_nil, Nat.add_zero]
      unfold maxKeySize at this; unfold bboltEntryMax; omega

theorem pageWsAs_mem {pg : List w8} {src : Src} {w : WEntry} (hw : w ∈ pageWsAs pg src) :
    ∃ i < pageCount pg, w.key = (pageW pg i).key ∧ w.value = (pageW pg i).value := by
  unfold pageWsAs pageWs at hw
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw'
  exact ⟨i, List.mem_range.1 hi, rfl, rfl⟩

theorem pageWsAs_length (pg : List w8) (src : Src) : (pageWsAs pg src).length = pageCount pg := by
  unfold pageWsAs pageWs; simp

/-- **The root bucket's node clause across materializations** (`rootPage_shape` for the new
nodes). -/
theorem rootNodes_matGrow (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) :
    ∀ {Y Z : WX} {bl : Loc}, matGrow Y Z bl → bl = X0.rl → matGrow X Y X0.rl →
      (∀ B, Y.t.bs !! X0.rl = some B → rootNodesOK B) →
      ∀ B, Z.t.bs !! X0.rl = some B → rootNodesOK B := by
  intro Y Z bl h
  induction h with
  | refl => intro _ _ h; exact h
  | step Y Y2 Z bl l pgid parent hadd hpos hm ih =>
    intro hbl hXY hY
    subst hbl
    apply ih rfl (Write.matGrow_snoc _ _ _ _ _ _ _ hXY hadd hpos)
    have hsh := rootPage_shape hI hXY hadd hpos
    obtain ⟨B, pa, pg, r, ns', bv', hB, hwp, -, -, -, -, hpar, -, hlf, -, -, -, -, hdat, -, -,
      -, -, -, -, hcase, hX'⟩ := hadd
    obtain ⟨s1, s2, s3⟩ := hsh B pa pg hB hwp
    intro B' hB'
    rw [hX'] at hB'
    have e : (Y.t.bs.insert X0.rl { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) !!
        X0.rl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } :=
      GMap.lookup_insert _ _ _
    rw [show (Y.t.bs.insert X0.rl _ : GMap Loc BRec) = _ from rfl, e] at hB'
    cases hB'
    have hold := hY B hB
    have hlen : r.ws.length = pageCount pg := by
      rw [← pageWsAs_length pg (posSrc B)]; exact length_of_dat hdat
    have hnew : ((r.nv.parent' ≠ null → 0 < r.ws.length) ∧
        (r.nv.isLeaf' = false → 2 ≤ r.ws.length)) ∧
        ∀ w ∈ r.ws, 0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax := by
      refine ⟨⟨fun h => by rw [hlen]; exact s1 (by rw [← hpar]; exact h), fun h => ?_⟩, ?_⟩
      · rw [hlen]; apply s2; intro e; rw [hlf, e] at h; simp at h
      · intro w hw
        obtain ⟨w', hw', he⟩ := mem_of_dat hdat hw
        obtain ⟨i, hi, hk, hv⟩ := pageWsAs_mem hw'
        rw [wDat_key he, wDat_value he, hk, hv]
        exact s3 i hi
    intro x rx hx
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, hws, -, -, -, -, hnv, rfl⟩
    · by_cases e : x = l
      · subst e; rw [GMap.lookup_insert] at hx; cases hx; exact hnew
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hx; exact hold x rx hx
    · by_cases e : x = l
      · subst e; rw [GMap.lookup_insert] at hx; cases hx; exact hnew
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hx
        by_cases ep : x = parent
        · subst ep
          rw [GMap.lookup_insert] at hx; cases hx
          obtain ⟨⟨o1, o2⟩, o3⟩ := hold x rp hrp
          have hp' : rx.nv.parent' = rp.nv.parent' := by rw [hnv]
          have hl' : rx.nv.isLeaf' = rp.nv.isLeaf' := by rw [hnv]
          rw [hws, hp', hl']
          exact ⟨⟨o1, o2⟩, o3⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm ep)] at hx; exact hold x rx hx

theorem spP_eq {X X' : WX} (hb : X'.t.bufs = X.t.bufs) (hv : X'.v = X.v) : spP X' = spP X := by
  unfold spP WX.bufPages; rw [hb, hv]

/-- A visited child's state depends on the writer only through `spP` and the mark. -/
theorem childSt_val {X0 X X' : WX} {w : WDb} {txid : w64} {c : Loc} {D : List Nat} {v : List w8}
    {p p' : Bool} (hP : spP X' = spP X) (hm : X'.t.mv = X.t.mv)
    (h : childSt X0 X w txid c D (.val v p)) : childSt X0 X' w txid c D (.val v p') := by
  unfold childSt at h ⊢; rw [hP, hm]; exact h

/-- **The staged value put into the root bucket's leaf** (see the module doc). -/
theorem rinv_put' (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {v : List w8} (hks : ks k = .val v false) (hc : B0.bm !! k = some c) {X1 : WX}
    (hm : matGrow X X1 X0.rl) {els : List elemRef} {pids : List w64}
    (hp : lPath X X0.rl els pids) (hr : lRoutes X X0.rl els pids k) {B1 : BRec} {pid : w64}
    {l : Loc} {rl : NRec} (hB1 : X1.t.bs !! X0.rl = some B1) (hlast : pids.getLast? = some pid)
    (hres : resolve B1 pid = some l) (hrl : B1.ns !! l = some rl) (s : GoSlice)
    (ins : List Inode) (hins : ins.length = (wsPutAt rl.ws k (rootEnt k v)).length)
    (hent : ∃ we ∈ X.allEnts X0.rl, we.key = k ∧ isBktFlag we.flags) :
    RInv X0 w0 B0 keys Lroot
      (X1.setNode X0.rl l (rl.withEnts s ins (wsPutAt rl.ws k (rootEnt k v)))) w st Dc
      (upd ks k (.val v true)) := by
  have h0 : ∀ B, X.t.bs !! X0.rl = some B → B.ib.root' ≠ W64 0 := by
    intro B hB; rw [hI.rootIb B hB]; exact hI.rootPg
  have hloc := hI.rootOK.1
  obtain ⟨hloc1, hv1, hmv1, -, hlt1⟩ := matGrow_keep hm hloc h0
  obtain ⟨f_rl, f_lB, f_bufs, f_pm, f_mv, f_v, f_oth, f_root, f_live, f_fuel⟩ := matGrow_frame hm
  have hG1 := spG_matGrow hm hloc h0 hI.G
  obtain ⟨B, hB, hbk0, hbm0⟩ := hI.root
  obtain ⟨B1', hB1', hbm1, hbk1, hib1⟩ := f_root B hB
  rw [hB1] at hB1'; cases hB1'
  have hrlX : X.rl = X0.rl := hI.rl
  -- the root bucket's facts in `X1`
  have hloc1' := hloc1
  obtain ⟨-, Bc, hBc, hcl, ⟨bnd, hbk⟩, -, -, hvw1⟩ := hloc1'
  rw [hB1] at hBc; cases hBc
  have hnc := hcl.2.2.2.2.2.2.2.1 l rl hrl
  -- the route's leaf
  have hR : LR.lRoute (ltree X1) X0.rl k pids :=
    LR.lRoute_ldat _ _ _ _ _ (LR.lRoute_of X X0.rl els pids k hp hr) (fun q _ => hlt1 q)
  have hrp : X1.rootPid X0.rl = X.rootPid X0.rl := by
    unfold WX.rootPid; rw [hB1, hB]; simp [hib1]
  have hh : pids.head? = some (X1.rootPid X0.rl) := by rw [hrp]; exact hp.2.2.1
  obtain ⟨last, b', ws, hgl, hL, hmem, -, hkin⟩ :=
    LR.route_main X1 X0.rl B1 bnd _ hB1 hcl hbk hvw1 k pids hR hh
  rw [hlast] at hgl; cases hgl
  have hLt : ltree X1 X0.rl pid = some (rl.nv.isLeaf', rl.ws) := by
    unfold ltree; rw [hB1]; simp [hres, hrl]
  rw [hLt] at hL
  simp only [Option.some.injEq, Prod.mk.injEq] at hL
  obtain ⟨hleaf, hws⟩ := hL
  subst hws
  have hwalk := LR.bInvL_walk X1 X0.rl B1 bnd _ hB1 hcl hbk hvw1 X1.fuel _ _
    (LR.bInvL_root X1 X0.rl B1 bnd _ hB1 hcl hbk hvw1)
  -- the leaves by data
  have hleavesD : (X1.leaves X0.rl).map (List.map wDat) =
      (X.leaves X0.rl).map (List.map wDat) := by
    unfold WX.leaves
    rw [f_fuel, hrp]
    exact Write.lleaves_dat _ _ X0.rl hlt1 _ _
  have hall1 : X1.allEnts X0.rl =
      ((Write.lleavesB (ltree X1) X0.rl X1.fuel (X1.rootPid X0.rl) (none, none)).map
        fun x => x.2.2).flatten := by
    unfold WX.allEnts WX.leaves; rw [Write.lleavesB_snd]
  -- a block holding `k` is the route's
  have huniq : ∀ x ∈ Write.lleavesB (ltree X1) X0.rl X1.fuel (X1.rootPid X0.rl) (none, none),
      ∀ w ∈ x.2.2, w.key = k → x = (pid, b', rl.ws) := by
    intro x hx w hw hwk
    apply Classical.byContradiction
    intro hne
    have hkx := hwalk.1 x hx w hw
    have := LR.pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hwalk.2.1 x hx _ hmem hne
    rw [hwk] at hkx
    exact this k hkx hkin
  -- the child's entry, in the route's leaf
  have hD1 : (X.allEnts X0.rl).map wDat = (X1.allEnts X0.rl).map wDat := by
    unfold WX.allEnts; rw [List.map_flatten, List.map_flatten, hleavesD]
  obtain ⟨we, hwe, hwk, hwf⟩ := hent
  obtain ⟨we1, hwe1, hd1⟩ := mem_of_dat hD1 hwe
  have hk1 : we1.key = k := (wDat_key hd1).symm.trans hwk
  have hf1 : isBktFlag we1.flags := by
    have := congrArg (fun d => d.1) hd1; simp only [wDat] at this; rw [← this]; exact hwf
  have hin : we1 ∈ rl.ws := by
    rw [hall1, List.mem_flatten] at hwe1
    obtain ⟨L, hL, hw⟩ := hwe1
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hL
    rw [huniq x hx we1 hw hk1] at hw; exact hw
  have hpw : Write.wsPw rl.ws := Write.wsSorted_pw _ hnc.2.2.2.1
  have hfound : wsFound rl.ws k := by
    have := LR.wsFound_of_mem rl.ws hpw we1 hin; rwa [hk1] at this
  have hbkt : ∀ w ∈ rl.ws, w.key = k → isBktFlag w.flags := by
    intro w hw e; rw [wsPw_key_inj hpw hw hin (e.trans hk1.symm)]; exact hf1
  have hkpos : 0 < k.length := by rw [← hwk]; exact (hI.entKeys we hwe).1
  have hkmax : k.length ≤ maxKeySize := by rw [← hwk]; exact (hI.entKeys we hwe).2
  have hkv : k.length + v.length ≤ bboltEntryMax := by
    have hk := hI.kids k c hc
    rw [hks] at hk
    obtain ⟨-, -, -, -, hvl⟩ := hk
    unfold maxKeySize at hkmax; unfold bboltEntryMax; omega
  have hwsP : wsPutAt rl.ws k (rootEnt k v) = rl.ws.set (wsIdx rl.ws k) (rootEnt k v) := by
    rw [Write.wsPutAt_eq, if_pos hfound]
  have hmemP : ∀ x ∈ wsPutAt rl.ws k (rootEnt k v), x = rootEnt k v ∨ x ∈ rl.ws := by
    intro x hx; rw [hwsP] at hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hlenP : (wsPutAt rl.ws k (rootEnt k v)).length = rl.ws.length := by
    rw [hwsP, List.length_set]
  -- the record and the writer after the put
  obtain ⟨r', hr'⟩ : ∃ r', r' = rl.withEnts s ins (wsPutAt rl.ws k (rootEnt k v)) := ⟨_, rfl⟩
  rw [← hr']
  have r_ws : r'.ws = wsPutAt rl.ws k (rootEnt k v) := by rw [hr']; rfl
  have r_lf : r'.nv.isLeaf' = rl.nv.isLeaf' := by rw [hr']; rfl
  have r_par : r'.nv.parent' = rl.nv.parent' := by rw [hr']; rfl
  have r_q : nodeQ rl r' := by rw [hr']; exact ⟨rfl, rfl⟩
  have r_bk : r'.nv.bucket' = rl.nv.bucket' := by rw [hr']; rfl
  have r_key : r'.nv.key' = rl.nv.key' ∧ r'.key = rl.key ∧ r'.ksrc = rl.ksrc := by
    rw [hr']; exact ⟨rfl, rfl, rfl⟩
  have hX1rl : X1.rl = X0.rl := f_rl.trans hrlX
  obtain ⟨X', hX'⟩ : ∃ X', X' = X1.setNode X0.rl l r' := ⟨_, rfl⟩
  rw [← hX']
  have x_rl : X'.rl = X0.rl := by rw [hX', setNode_rl]; exact hX1rl
  have x_v : X'.v = X.v := by rw [hX', setNode_v]; exact f_v
  have x_mv : X'.t.mv = X.t.mv := by rw [hX', setNode_mv]; exact f_mv
  have x_bufs : X'.t.bufs = X.t.bufs := by rw [hX', setNode_bufs]; exact f_bufs
  have x_pm : X'.t.pm = X.t.pm := by rw [hX', setNode_pm]; exact f_pm
  have x_lB : X'.liveB = X.liveB := by rw [hX', setNode_liveB]; exact f_lB
  have x_fuel : X'.fuel = X.fuel := by rw [hX', setNode_fuel hB1]; exact f_fuel
  have x_P : spP X' = spP X := spP_eq x_bufs x_v
  have x_root : X'.t.bs !! X0.rl = some { B1 with ns := B1.ns.insert l r' } := by
    rw [hX']; exact setNode_bs_self hB1
  have x_oth : ∀ c, c ≠ X0.rl → X'.t.bs !! c = X.t.bs !! c := by
    intro c hc; rw [hX', setNode_bs_other hB1 hc]; exact f_oth c hc
  -- the spill's global state
  have hwlP : wsLive r'.ws := by
    intro x hx; rw [r_ws] at hx
    rcases hmemP x hx with rfl | h
    · exact ⟨(by simp [rootEnt]), (by simp [rootEnt])⟩
    · exact hnc.2.2.2.2.2.1 x h
  have hkP : ∀ x ∈ r'.ws, 0 < x.key.length := by
    intro x hx; rw [r_ws] at hx
    rcases hmemP x hx with rfl | h
    · exact hkpos
    · exact hnc.2.2.2.2.1 x h
  have hkc := hnc.2.2.2.2.2.2.2.2.2.2.1
  have hG' : spG X' w0.wtxid (mapLen w.ms) w.fl := by
    rw [hX']
    refine spG_setNode (by unfold WX.node; rw [hB1]; exact hrl) r_q r_bk hkP ?_ hwlP ?_ hG1
    · rcases hkc with h | h
      · left; rw [r_key.1]; exact h
      · right; rw [r_key.2.1]; exact h.1
    · intro hn; rw [r_key.2.2]
      rcases hkc with h | h
      · rw [r_key.1] at hn; exact absurd h hn
      · exact h.2
  -- the root bucket's facts
  have hlocP : bktLocalOK X' X0.rl := by
    rw [hX', hr']
    refine bktLocalOK_putOpened X1 X0.rl l B1 rl s ins k (rootEnt k v) hloc1 hB1 hrl hleaf hfound
      rfl ?_ (Or.inr rfl) (by simp [rootEnt]) rfl (hins.trans hlenP)
    unfold opened; rw [hbm1, hbm0, hc]; rfl
  have hrtP : rtOK X' X0.rl := by
    obtain ⟨t, ht, htp, hth, D, hD⟩ := hI.rootOK.2.1
    obtain ⟨t1, ht1, hp1, hh1, hd1⟩ := ltIs_ldat (ltree X) (ltree X1) X0.rl hlt1 t ht
    have hrep : ∀ q, ltree X' X0.rl q = ltree X1 X0.rl q ∨ ∃ ws ws',
        ltree X1 X0.rl q = some (true, ws) ∧ ltree X' X0.rl q = some (true, ws') := by
      intro q
      rw [hX', setNode_ltree hB1 r_lf]
      by_cases hq : resolve B1 q = some l
      · right; refine ⟨rl.ws, r'.ws, ?_, ?_⟩
        · unfold ltree; rw [hB1]; simp [hq, hrl, hleaf]
        · rw [if_pos ⟨rfl, hq⟩, hleaf]
      · left; rw [if_neg (fun h => hq h.2)]
    obtain ⟨t2, ht2, hp2, hh2, hd2⟩ := ltIs_leafRep (ltree X1) (ltree X') X0.rl hrep t1 ht1
    refine ⟨t2, ht2, ?_, ?_, D, ?_⟩
    · rw [hp2, hp1, htp, hX', setNode_rootPid hB1, hrp]
    · rw [hh2, hh1, x_fuel]; exact hth
    · intro x hx; rw [hd2, hd1] at hx; exact hD x hx
  have hnodes1 : rootNodesOK B1 := by
    refine rootNodes_matGrow hI hm rfl (matGrow.refl X X0.rl) (fun B' hB' => ?_) B1 hB1
    obtain ⟨-, -, B'', hB'', hn⟩ := hI.rootOK
    rw [hB'] at hB''; cases hB''; exact hn
  have hrootP : rootLoc X' X0.rl := by
    refine ⟨hlocP, hrtP, _, x_root, fun x rx hx => ?_⟩
    have hx' : (B1.ns.insert l r') !! x = some rx := hx
    by_cases e : x = l
    · subst e; rw [GMap.lookup_insert] at hx'; cases hx'
      obtain ⟨⟨o1, -⟩, o3⟩ := hnodes1 _ rl hrl
      refine ⟨⟨fun hpar => ?_, fun hl => ?_⟩, fun y hy => ?_⟩
      · rw [r_ws, hlenP]; exact o1 (r_par ▸ hpar)
      · rw [r_lf, hleaf] at hl; cases hl
      · rw [r_ws] at hy; rcases hmemP y hy with rfl | h
        · exact ⟨hkpos, hkv⟩
        · exact o3 y h
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hx'; exact hnodes1 x rx hx'
  -- the root entries
  have hents : rootEnts X' = (rootEnts X).map (repVal k v) := by
    have h1 := rootEnts_putAt (X := X1) (by rw [hX1rl]; exact hB1) hrl hleaf (r_lf.trans hleaf)
      r_ws hpw hfound hbkt rfl (by show isBktFlag (W32 1); unfold isBktFlag; decide) (by
        intro x hx hx' y hy hyk
        rw [hX1rl] at hx
        exact hx' (by rw [huniq x hx y hy hyk]; exact hres))
    have h2 : rootEnts X1 = rootEnts X :=
      Write.rootEnts_eq_of_dat X X1 (by rw [hX1rl, hrlX]; exact hleavesD)
    rw [hX', ← hX1rl, h1, h2]; rfl
  have hreach : liveReach X := hI.G.2.2.2.2.1
  exact {
    C := hI.C
    fl := hI.fl
    pages := by rw [x_v]; exact hI.pages
    rl := x_rl
    mark := by rw [x_mv]; exact hI.mark
    G := hG'
    root := ⟨_, x_root, hbk1.trans hbk0, hbm1.trans hbm0⟩
    rootOK := hrootP
    rootIb := by
      intro B' hB'; rw [x_root] at hB'; cases hB'; exact hib1.trans (hI.rootIb B hB)
    slots := by rw [x_mv]; exact hI.slots
    base := hI.base
    new := hI.new
    agree := by intro x hx; rw [x_P]; exact hI.agree x hx
    kids := by
      intro k' c' hc'
      have hold := hI.kids k' c' hc'
      unfold upd
      by_cases e : k' = k
      · subst e; rw [if_pos rfl]; rw [hks] at hold; exact childSt_val x_P x_mv hold
      · rw [if_neg e]
        cases hs : ks k' with
        | val v' p' => rw [hs] at hold; exact childSt_val x_P x_mv hold
        | nilc => rw [hs] at hold; exact hold
        | todo =>
          rw [hs] at hold
          have hne : c' ≠ X0.rl := by
            obtain ⟨C, -, -, -, hne, -⟩ := hold; rw [← hrlX]; exact hne
          refine childSt_kept hold ?_ ?_ (by rw [x_v]) (by rw [x_v, ← hv1]; exact hvw1)
            (Nat.le_of_eq (by rw [x_mv])) x_lB (x_rl.trans hrlX.symm) hreach hG'.2.2.1 hG'.2.2.2.1
            x_fuel (fun x _ => by rw [x_P]) (fun F _ hF id hid => by rw [x_pm]; exact hF id hid)
          · intro C hC
            exact ⟨C, by rw [x_oth c' hne]; exact hC, bktSim_refl C,
              fun _ => optRel_refl nodeSim_refl _⟩
          · intro C C' l0 r0 r0' hC hC' h1 h2 _ hvs
            rw [x_oth c' hne, hC] at hC'; cases hC'; rw [h1] at h2; cases h2; exact hvs
    ents := by
      rw [hents, hI.ents, List.map_map]
      apply List.map_congr_left
      intro e _
      obtain ⟨a, b⟩ := e
      by_cases h : a = k
      · subst h; simp [repVal, upd, KSt.entVal]
      · simp [repVal, upd, h]
    keysAll := hI.keysAll
    rootPg := hI.rootPg
    entKeys := by
      intro we' hwe'
      have hallP : X'.allEnts X0.rl = ((Write.lleavesB (ltree X1) X0.rl X1.fuel
          (X1.rootPid X0.rl) (none, none)).map fun x =>
            (if decide (X0.rl = X0.rl ∧ resolve B1 x.1 = some l) then (x.1, x.2.1, r'.ws)
              else x).2.2).flatten := by
        unfold WX.allEnts WX.leaves
        rw [← Write.lleavesB_snd, hX', setNode_blocks hB1 hrl hleaf (r_lf.trans hleaf),
          List.map_map]
        rfl
      rw [hallP, List.mem_flatten] at hwe'
      obtain ⟨L, hL, hw⟩ := hwe'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hL
      by_cases hs : resolve B1 x.1 = some l
      · rw [if_pos (decide_eq_true ⟨rfl, hs⟩)] at hw
        rw [r_ws] at hw
        rcases hmemP we' hw with rfl | h
        · exact ⟨hkpos, hkmax⟩
        · have hw1 : we' ∈ X1.allEnts X0.rl := by
            rw [hall1, List.mem_flatten]; exact ⟨_, List.mem_map.2 ⟨_, hmem, rfl⟩, h⟩
          obtain ⟨we0, hwe0, hk0⟩ := allEnts_kept hleavesD hw1
          rw [hk0]; exact hI.entKeys we0 hwe0
      · rw [if_neg (by simp [hs])] at hw
        have hw1 : we' ∈ X1.allEnts X0.rl := by
          rw [hall1, List.mem_flatten]; exact ⟨_, List.mem_map.2 ⟨x, hx, rfl⟩, hw⟩
        obtain ⟨we0, hwe0, hk0⟩ := allEnts_kept hleavesD hw1
        rw [hk0]; exact hI.entKeys we0 hwe0
    rootBkt := by
      intro we' hwe'
      have hallP : X'.allEnts X0.rl = ((Write.lleavesB (ltree X1) X0.rl X1.fuel
          (X1.rootPid X0.rl) (none, none)).map fun x =>
            (if decide (X0.rl = X0.rl ∧ resolve B1 x.1 = some l) then (x.1, x.2.1, r'.ws)
              else x).2.2).flatten := by
        unfold WX.allEnts WX.leaves
        rw [← Write.lleavesB_snd, hX', setNode_blocks hB1 hrl hleaf (r_lf.trans hleaf),
          List.map_map]
        rfl
      rw [hallP, List.mem_flatten] at hwe'
      obtain ⟨L, hL, hw⟩ := hwe'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hL
      by_cases hs : resolve B1 x.1 = some l
      · rw [if_pos (decide_eq_true ⟨rfl, hs⟩)] at hw
        rw [r_ws] at hw
        rcases hmemP we' hw with rfl | h
        · show isBktFlag (W32 1); unfold isBktFlag; decide
        · have hw1 : we' ∈ X1.allEnts X0.rl := by
            rw [hall1, List.mem_flatten]; exact ⟨_, List.mem_map.2 ⟨_, hmem, rfl⟩, h⟩
          obtain ⟨we0, hwe0, hk0⟩ := allEnts_keptF hleavesD hw1
          rw [hk0]; exact hI.rootBkt we0 hwe0
      · rw [if_neg (by simp [hs])] at hw
        have hw1 : we' ∈ X1.allEnts X0.rl := by
          rw [hall1, List.mem_flatten]; exact ⟨_, List.mem_map.2 ⟨x, hx, rfl⟩, hw⟩
        obtain ⟨we0, hwe0, hk0⟩ := allEnts_keptF hleavesD hw1
        rw [hk0]; exact hI.rootBkt we0 hwe0
    inj := hI.inj
    cok := hI.cok
    bufs := by
      have := hI.bufs; unfold bufsOK at this ⊢; rw [x_bufs, x_mv]; exact this
    grow := markGrow_congr hI.grow x_bufs (by rw [x_mv])
    rootPos := by
      intro B' hB'
      rw [x_root] at hB'; cases hB'
      refine rootUnder_setLeaf ?_ (by rw [r_lf]; exact hleaf)
      exact rootUnder_matGrow hm hloc h0 hI.pages hI.rootPos B1 hB1
    shape0 := hI.shape0
    hwm0 := hI.hwm0
    freeNC := hI.freeNC
    tt := by rw [hX', setNode_tt, matGrow_tt hm]; exact hI.tt
    same := fun h => absurd h (same_upd_val (hI.keysAll k (by rw [hc]; rfl)) _ _)
    putRoot := by
      intro _ B' hB' hnull
      rw [x_root] at hB'; cases hB'
      obtain ⟨-, Bc', hBc', hcl', -⟩ := hloc1
      rw [hB1] at hBc'; cases hBc'
      have he := (hcl'.2.2.1 hnull).1
      rw [he] at hrl
      simp at hrl
    mvEq := by rw [x_mv]; exact hI.mvEq
    rootFree := fun F hF id hid => by rw [x_pm]; exact hI.rootFree F hF id hid
    lroot := hI.lroot
    rootExt := by
      rw [hX', extents_setLeaf hB1 hrl hleaf (r_lf.trans hleaf) (by rw [hr']; rfl),
        extents_matGrow hm hloc h0]
      exact hI.rootExt
    notKeys := notKeys_upd hI.notKeys (hI.keysAll k (by rw [hc]; rfl))
    nilKids := by
      refine nilKids_upd hI (nilKids_self_val hI hks _) ?_
      intro k' c' Cx _ hc' htd hCx hn C' hC'
      have hold := hI.kids k' c' hc'
      rw [htd] at hold
      have hne : c' ≠ X0.rl := by
        obtain ⟨C, -, -, -, hne, -⟩ := hold; rw [← hrlX]; exact hne
      rw [x_oth c' hne, hCx] at hC'; cases hC'; exact hn }

end rput

end Spill

end bbolt
end EtcdGrove
end Perennial
