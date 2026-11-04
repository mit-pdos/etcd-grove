/-
`node.spill` after its children's loop (U9y, `notes/bbolt-proof-plan.md`; pure): **the states a
piece's step** (`pcStep`) leaves.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesStep
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesAlloc
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureG
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureAlloc
public import Proof.go_etcd_io.bbolt.Spill.AllocDeref
public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Spill.SlotInv
public import Proof.go_etcd_io.bbolt.Spill.TreeDataSpill

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section state
variable [GooseExts] [GoGlobalContext]

/-- **The spill's global state after a piece's step.** -/
theorem pcStepX_spG {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hlv : l ∈ Xi.live) (hne : rl.nv.parent' ≠ null → 0 < rl.ws.length)
    (hpl : rl.nv.parent' ≠ null → rl.nv.parent' ≠ l ∧ rl.nv.parent' ∈ Xi.live)
    (hd : objsDisj Xi.t)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl)
    (hfl : ∀ y ∈ wi.fl.allIds, y.toNat < Xi.t.mv.pgid'.toNat)
    (hfv : ∀ y ∈ wi.fl.free, Xi.v.pages !! y.toNat = none)
    (hvb : ∀ y pg, Xi.v.pages !! y = some pg → y < Xi.t.mv.pgid'.toNat) :
    spG X3 wi.wtxid (mapLen w2.ms) w2.fl := by
  sorry

/-- **The frame of a piece's step**: the piece and its parent touched. -/
theorem pcStepX_frame {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hd : objsDisj Xi.t)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl) :
    spFrame Xi X3 bl [l, rl.nv.parent'] := by
  sorry

/-- **A piece's step is a spill step** for the slots `O` (owned with `L`, which holds the piece's
own page, if any). -/
theorem pcStepX_step {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} {O L : List Nat} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl)
    (hG3 : spG X3 wi.wtxid (mapLen w2.ms) w2.fl)
    (hsl : slotInv wi.fl Xi.t.mv.pgid'.toNat (O ++ L))
    (hown : rl.nv.pgid' ≠ W64 0 → rl.nv.pgid'.toNat ∈ L) :
    spStep Xi X3 wi w2 O st := by
  sorry

theorem setNode_t_mv (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.mv = X.t.mv := by
  unfold WX.setNode; split <;> rfl

theorem setNode_t_bufs (X : WX) (bl l : Loc) (r : NRec) :
    (X.setNode bl l r).t.bufs = X.t.bufs := by
  unfold WX.setNode; split <;> rfl

theorem setNode_t_pm (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.pm = X.t.pm := by
  unfold WX.setNode; split <;> rfl

/-- **A piece's free** keeps all but the piece's record and the freelist's pending part. -/
theorem pcFreed_basic {X X1 : WX} {w w1 : WDb} {bl l : Loc} {r : NRec} {st : List FLStep}
    (h : pcFreed X w bl l r X1 w1 st) :
    X1.t.mv = X.t.mv ∧ X1.t.bufs = X.t.bufs ∧ X1.t.pm = X.t.pm ∧ X1.v = X.v ∧
    X1.live = X.live ∧ w1.C = w.C ∧ w1.ms = w.ms ∧ w1.fl.free = w.fl.free ∧
    w1.fl = w.fl.applySteps w.wtxid st := by
  rcases h with ⟨-, rfl, rfl, rfl⟩ | ⟨pg, -, -, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨setNode_t_mv _ _ _ _, setNode_t_bufs _ _ _ _, setNode_t_pm _ _ _ _,
      WX.setNode_v _ _ _ _, WX.setNode_live _ _ _ _, rfl, rfl, rfl, rfl⟩

/-- **The allocated run is no owned slot.** -/
theorem pcStepX_fresh {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} {L : List Nat} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hsl : slotInv wi.fl Xi.t.mv.pgid'.toNat L) :
    ∀ s ∈ L, s < id.toNat ∨ id.toNat + count ≤ s := by
  obtain ⟨X1, w1, X2, p, ra, rp, s, ins, stf, sta, hfr, -, hal, -⟩ := hs
  obtain ⟨hmv, -, -, -, -, -, -, hfree, -⟩ := pcFreed_basic hfr
  obtain ⟨-, -, Xr, -, hX'⟩ := hal
  intro y hy
  obtain ⟨hy1, hy2, hy3⟩ := hsl.2.1 y hy
  rcases hX' with ⟨hcan, -, -⟩ | ⟨hid, -, -, -⟩
  · by_cases hr : id.toNat ≤ y ∧ y < id.toNat + count
    · exfalso
      have hin : inRun id count (W64 (y : Int)) := by
        unfold inRun; rw [w64_toNat_of_lt hy2]; exact hr
      have := hcan.2 _ hin
      rw [hfree] at this
      exact hy3 (List.mem_append_left _ this)
    · omega
  · left; rw [hid, hmv]; exact hy1

/-- **The slots after a piece's step**: the piece's own page's (`A`) freed, the run allocated. -/
theorem pcStepX_slot {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} {O L : List Nat} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl)
    (hsl : slotInv wi.fl Xi.t.mv.pgid'.toNat (O ++ (ownSl Xi.v rl.nv.pgid' ++ L))) :
    slotInv w2.fl X3.t.mv.pgid'.toNat (O ++ L ++ List.range' id.toNat count) := by
  obtain ⟨X1, w1, X2, p, ra, rp, s, ins, stf, sta, hfr, -, hal, -, -, -, -, -, -, rfl⟩ := hs
  have hG := hG1 X1 w1 stf hfr
  obtain ⟨hmv, -, -, -, -, -, -, -, -⟩ := pcFreed_basic hfr
  have hsl1 : slotInv w1.fl Xi.t.mv.pgid'.toNat (O ++ L) := by
    rcases hfr with ⟨hp0, rfl, rfl, rfl⟩ | ⟨pg, hp0, hpg, rfl, rfl, rfl⟩
    · unfold ownSl at hsl; rw [if_pos hp0] at hsl; exact hsl
    · unfold ownSl at hsl
      rw [if_neg hp0] at hsl
      have he : pgSlots Xi.v.pages [rl.nv.pgid'.toNat] =
          List.range' rl.nv.pgid'.toNat (1 + pageOverflow pg) := by
        unfold pgSlots; simp [hpg]
      rw [he] at hsl
      refine slotInv_free (slotInv_perm ?_ hsl)
      rw [List.perm_iff_count]; intro a; simp only [List.count_append]; omega
  have hmv3 : (pcFin X2 bl l ra rl.nv.parent' rp s ins id count
      (decide (rl.nv.parent' ≠ null))).t.mv = X2.t.mv := by
    unfold pcFin WX.setBuf; split <;> simp only [setNode_t_mv]
  rw [hmv3]
  obtain ⟨hc, -, Xr, -, hX'⟩ := hal
  rcases hX' with ⟨hcan, hfl', rfl⟩ | ⟨hid, hfl', hlt, rfl⟩
  · rw [addPage_pgid, hfl']
    rw [← hmv] at hsl1
    exact slotInv_alloc hsl1 (Nat.le_of_lt hG.2.2.2.2.2.2.1) hcan
  · rw [addPage_pgid, hfl']
    rw [← hmv, ← hid] at hsl1
    have : (id + W64 (count : Int)).toNat = id.toNat + count := by word
    rw [hid, ← hid, this]
    exact slotInv_allocHwm hsl1 hlt

/-- The writer's buffers' map by id. -/
theorem bufPages_get (X : WX) (k : w64) : X.bufPages !! k.toNat = X.t.bufs !! k := by
  unfold WX.bufPages
  rw [ofList_lookup_find]
  cases hf : (X.t.bufs.toList.map fun e => (e.1.toNat, e.2)).find?
      (fun e => decide (e.1 = k.toNat)) with
  | none =>
    simp only [Option.map_none]
    cases e : X.t.bufs !! k with
    | none => rfl
    | some bs =>
      have hm : (k.toNat, bs) ∈ X.t.bufs.toList.map fun e => (e.1.toNat, e.2) :=
        List.mem_map.2 ⟨(k, bs), (GMap.mem_toList _ k bs).2 e, rfl⟩
      have := List.find?_eq_none.1 hf _ hm
      simp at this
  | some e =>
    simp only [Option.map_some]
    have hm := List.mem_of_find?_eq_some hf
    have he : e.1 = k.toNat := by simpa using List.find?_some hf
    obtain ⟨⟨k', bs⟩, hk, rfl⟩ := List.mem_map.1 hm
    simp only at he ⊢
    have : k' = k := BitVec.eq_of_toNat_eq he
    subst this
    exact ((GMap.mem_toList _ k' bs).1 hk).symm

/-- A slot past `2 ^ 64` is no buffer. -/
theorem bufPages_big (X : WX) (y : Nat) (hy : 2 ^ 64 ≤ y) : X.bufPages !! y = none := by
  unfold WX.bufPages
  rw [ofList_lookup_find]
  cases hf : (X.t.bufs.toList.map fun e => (e.1.toNat, e.2)).find?
      (fun e => decide (e.1 = y)) with
  | none => rfl
  | some e =>
    have hm := List.mem_of_find?_eq_some hf
    have he : e.1 = y := by simpa using List.find?_some hf
    obtain ⟨⟨k', bs⟩, -, rfl⟩ := List.mem_map.1 hm
    simp only at he
    have := k'.isLt; omega

/-- The spill's page map after a buffer `id` is (re)written, the view's pages kept. -/
theorem spP_bufs_insert {X X' : WX} {id : w64} {pg : List w8}
    (hb : X'.t.bufs = X.t.bufs.insert id pg) (hv : X'.v.pages = X.v.pages) :
    spP X' !! id.toNat = some pg ∧ ∀ y, y ≠ id.toNat → spP X' !! y = spP X !! y := by
  refine ⟨?_, fun y hy => ?_⟩
  · unfold spP; rw [GMap.lookup_union, bufPages_get, hb, GMap.lookup_insert]; rfl
  · unfold spP
    rw [GMap.lookup_union, GMap.lookup_union, hv]
    congr 1
    by_cases hy64 : y < 2 ^ 64
    · have e : y = (W64 (y : Int)).toNat := by word
      rw [e, bufPages_get, bufPages_get, hb, GMap.lookup_insert_ne]
      intro he; apply hy; rw [e, he]
    · rw [bufPages_big _ _ (by omega), bufPages_big _ _ (by omega)]

/-- **What a successful `allocate` changes**: the buffer and page-cache entry `id`, the mark (at
the free ids, unchanged; at the mark, past the run). -/
theorem allocRes_basic {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} (h : allocRes X X' fl fl' txid count p id) :
    X'.v.pages = X.v.pages ∧ X'.live = X.live ∧ X'.t.mv.txid' = X.t.mv.txid' ∧
    X'.t.bufs = X.t.bufs.insert id
      (encode (⟨id, W16 0, W16 0, W32 ((count - 1 : Nat) : Int)⟩ : Page) ++
        List.replicate (count * 4096 - 16) (W8 0)) ∧
    ((fl.canAlloc id count ∧ fl' = fl.alloc txid id count ∧ X'.t.mv.pgid' = X.t.mv.pgid') ∨
     (id = X.t.mv.pgid' ∧ fl' = fl ∧ id.toNat + count < 2 ^ 62 ∧
       X'.t.mv.pgid'.toNat = id.toNat + count)) := by
  obtain ⟨-, -, Xr, hXr, hX'⟩ := h
  have hR : Xr.v.pages = X.v.pages ∧ Xr.live = X.live ∧ Xr.t.mv = X.t.mv ∧
      Xr.t.bufs = X.t.bufs := by
    rcases hXr with rfl | ⟨Xd, b, hdr, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨(congrArg View.pages hdr.2.1 : Xd.v.pages = X.v.pages), hdr.2.2.1, hdr.2.2.2.2.2.2.1,
        hdr.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨h1, h2, h3, h4⟩ := hR
  rcases hX' with ⟨hc, hf, rfl⟩ | ⟨hid, hf, hlt, rfl⟩
  · refine ⟨h1, h2, by simp only [WX.addPage, h3], by simp only [WX.addPage, h4],
      Or.inl ⟨hc, hf, by simp only [WX.addPage, h3]⟩⟩
  · refine ⟨h1, h2, by simp only [WX.addPage, h3], by simp only [WX.addPage, h4],
      Or.inr ⟨hid, hf, hlt, ?_⟩⟩
    simp only [WX.addPage]; try word

/-- **The records and buffers after a piece's step**: the piece's record written (`pcRec`) over
its record after the allocation `ra` (its own but the sources and page id), the parent's with its
entry (`pcPar`, over its record modulo sources), the buffer `id` the written page; the view's
pages, the live nodes and the txid kept, the mark not lower, the run `id … id + count - 1` below
it. -/
theorem pcStepX_state {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hpl : rl.nv.parent' ≠ null → rl.nv.parent' ≠ l)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl)
    (hfl : ∀ y ∈ wi.fl.free, y.toNat < Xi.t.mv.pgid'.toNat) :
    ∃ ra rp s ins q, X3.node bl l = some (pcRec ra id (decide (rl.nv.parent' ≠ null))) ∧
      nodeSim { rl with nv := { rl.nv with pgid' := q } } ra ∧
      (rl.nv.parent' ≠ null → ∀ rpi, Xi.node bl rl.nv.parent' = some rpi →
        X3.node bl rl.nv.parent' = some (pcPar rp ra id s ins) ∧ nodeSim rpi rp ∧
        ins.length = (wsPutAt rp.ws (pcOldKey ra) (pcEnt ra id)).length ∧ ra.k0 ≠ slice.nil) ∧
      X3.live = Xi.live ∧ X3.v.pages = Xi.v.pages ∧ X3.t.mv.txid' = Xi.t.mv.txid' ∧
      Xi.t.mv.pgid'.toNat ≤ X3.t.mv.pgid'.toNat ∧ id.toNat + count ≤ X3.t.mv.pgid'.toNat ∧
      0 < count ∧
      X3.t.bufs = Xi.t.bufs.insert id (pcPage id ra.nv.isLeaf' ra.ws count) ∧
      Xi.t.bufs !! id = none := by
  obtain ⟨X1, w1, X2, p, ra, rp, s, ins, stf, sta, hfr, -, hal, -, -, -, -, hra, hrp, rfl⟩ := hs
  have hG := hG1 X1 w1 stf hfr
  obtain ⟨hmv, hbf, -, hv1, hlv1, -, -, hfree, -⟩ := pcFreed_basic hfr
  obtain ⟨hab1, hab2, hab3, hab4, hab5⟩ := allocRes_basic hal
  -- the piece's record after the free
  obtain ⟨q, hn1⟩ : ∃ q, X1.node bl l = some { rl with nv := { rl.nv with pgid' := q } } := by
    rcases hfr with ⟨-, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
    · exact ⟨rl.nv.pgid', hn⟩
    · exact ⟨W64 0, WX.setNode_node_same hn _⟩
  obtain ⟨⟨ra', hra', hsa⟩, -⟩ := allocRes_node hal hn1
  rw [hra] at hra'; cases hra'
  have hc0 : 0 < count := hal.1
  -- the run
  have hrun : id.toNat + count ≤ X2.t.mv.pgid'.toNat ∧ Xi.t.mv.pgid'.toNat ≤ X2.t.mv.pgid'.toNat ∧
      Xi.t.bufs !! id = none := by
    have hb0 := hG.2.2.2.2.2.2.2.1 id
    rw [hbf] at hb0
    rcases hab5 with ⟨hcan, -, hm⟩ | ⟨hid, -, hlt, hm⟩
    · have hin : ∀ j < count, id + W64 (j : Int) ∈ w1.fl.free ∧
          (id + W64 (j : Int)).toNat = id.toNat + j := by
        intro j hj
        have ht : (id + W64 (j : Int)).toNat = id.toNat + j := by have := hcan.1; word
        exact ⟨hcan.2 _ (by unfold inRun; omega), ht⟩
      rw [hm, hmv]
      refine ⟨?_, Nat.le_refl _, ?_⟩
      · obtain ⟨h1, h2⟩ := hin (count - 1) (by omega)
        have := hfl _ (hfree ▸ h1); omega
      · cases e : Xi.t.bufs !! id with
        | none => rfl
        | some _ =>
          have h1 := (hin 0 (by omega)).1
          rw [show id + W64 ((0 : Nat) : Int) = id by word] at h1
          exact absurd h1 (hb0 (by simp [e])).2.1
    · have hidn : id.toNat = Xi.t.mv.pgid'.toNat := by rw [hid, hmv]
      refine ⟨by omega, by omega, ?_⟩
      cases e : Xi.t.bufs !! id with
      | none => rfl
      | some _ =>
        have := (hb0 (by simp [e])).1
        rw [← hid] at this; omega
  have hpf : ∀ (X : WX) (pg : List w8), (X.setBuf id pg).node = X.node := fun _ _ => rfl
  generalize hX3 : pcFin X2 bl l ra rl.nv.parent' rp s ins id count
    (decide (rl.nv.parent' ≠ null)) = X3
  have hmv3 : X3.t.mv = X2.t.mv := by
    rw [← hX3]; unfold pcFin WX.setBuf; split <;> simp only [setNode_t_mv]
  have hbf3 : X3.t.bufs = X2.t.bufs.insert id (pcPage id ra.nv.isLeaf' ra.ws count) := by
    rw [← hX3]; unfold pcFin WX.setBuf; split <;> simp only [setNode_t_bufs]
  have hlv3 : X3.live = X2.live := by
    rw [← hX3]; unfold pcFin WX.setBuf; split <;> simp only [WX.setNode_live]
  have hv3 : X3.v = X2.v := by
    rw [← hX3]; unfold pcFin WX.setBuf; split <;> simp only [WX.setNode_v]
  have hbuf : X3.t.bufs = Xi.t.bufs.insert id (pcPage id ra.nv.isLeaf' ra.ws count) := by
    rw [hbf3, hab4, hbf, GMap.insert_insert]
  have hcom : X3.live = Xi.live ∧ X3.v.pages = Xi.v.pages ∧ X3.t.mv.txid' = Xi.t.mv.txid' ∧
      Xi.t.mv.pgid'.toNat ≤ X3.t.mv.pgid'.toNat ∧ id.toNat + count ≤ X3.t.mv.pgid'.toNat := by
    rw [hlv3, hv3, hmv3, hab2, hlv1, hab1, hv1, hab3, hmv]
    exact ⟨rfl, rfl, rfl, hrun.2.1, hrun.1⟩
  by_cases hp : rl.nv.parent' ≠ null
  · have hpl' := hpl hp
    have hfin : X3 = ((X2.setNode bl l (pcRec ra id true)).setNode bl rl.nv.parent'
        (pcPar rp ra id s ins)).setBuf id (pcPage id ra.nv.isLeaf' ra.ws count) := by
      rw [← hX3]; unfold pcFin; rw [if_pos (by simpa using hp)]
    obtain ⟨hrp', hinsl, hk0⟩ := hrp hp
    refine ⟨ra, rp, s, ins, q, ?_, hsa, fun _ rpi hrpi => ⟨?_, ?_, hinsl, hk0⟩, hcom.1, hcom.2.1,
      hcom.2.2.1, hcom.2.2.2.1, hcom.2.2.2.2, hc0, hbuf, hrun.2.2⟩
    · rw [hfin, hpf, WX.setNode_node_ne _ _ (Ne.symm hpl'), decide_eq_true hp]
      exact WX.setNode_node_same hra _
    · rw [hfin, hpf]
      exact WX.setNode_node_same (by rw [WX.setNode_node_ne _ _ hpl']; exact hrp') _
    · have h1 : X1.node bl rl.nv.parent' = some rpi := by
        rcases hfr with ⟨-, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
        · exact hrpi
        · rw [WX.setNode_node_ne _ _ hpl']; exact hrpi
      obtain ⟨⟨r2, hr2, hs2⟩, -⟩ := allocRes_node hal h1
      rw [hrp'] at hr2; cases hr2; exact hs2
  · have hfin : X3 = (X2.setNode bl l (pcRec ra id false)).setBuf id
        (pcPage id ra.nv.isLeaf' ra.ws count) := by
      rw [← hX3]; unfold pcFin; rw [if_neg (by simpa using hp)]
    refine ⟨ra, rp, s, ins, q, ?_, hsa, fun h' => absurd h' hp, hcom.1, hcom.2.1,
      hcom.2.2.1, hcom.2.2.2.1, hcom.2.2.2.2, hc0, hbuf, hrun.2.2⟩
    rw [hfin, hpf, decide_eq_false hp]
    exact WX.setNode_node_same hra _

end state

end Spill

end bbolt
end EtcdGrove
end Perennial
