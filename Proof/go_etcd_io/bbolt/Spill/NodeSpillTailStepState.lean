/-
`node.spill` after its children's loop (U9y, `notes/bbolt-proof-plan.md`; pure): **the corrected
piece step** `pcStepX` (see `Spill/NodeSpillTailStep`'s module doc) and the states its parts leave.
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

section defs
variable [GooseExts]

/-- **A piece's step, corrected** (`pcStep` and: the allocation's freelist steps `sta` after the
free's `stf`; with a parent, its inodes' count its entries' after the put, and the piece's key
slice not nil). -/
def pcStepX (X : WX) (w : WDb) (bl l : Loc) (r : NRec) (count : Nat) (X3 : WX) (w2 : WDb)
    (st : List FLStep) (id : w64) : Prop :=
  ∃ X1 w1 X2 p ra rp s ins stf sta, pcFreed X w bl l r X1 w1 stf ∧ st = stf ++ sta ∧
    allocRes X1 X2 w1.fl w2.fl w.wtxid count p id ∧ w2.fl = w1.fl.applySteps w.wtxid sta ∧
    w2.C = w1.C ∧
    X2.t.mv.pgid'.toNat * 4096 ≤ mapLen w2.ms ∧ (w2 = w1.withFl w2.fl ∨ wdbRemap w1 w2) ∧
    X2.node bl l = some ra ∧
    (r.nv.parent' ≠ null → X2.node bl r.nv.parent' = some rp ∧
      ins.length = (wsPutAt rp.ws (pcOldKey ra) (pcEnt ra id)).length ∧ ra.k0 ≠ slice.nil) ∧
    X3 = pcFin X2 bl l ra r.nv.parent' rp s ins id count (decide (r.nv.parent' ≠ null))

end defs

section state
variable [GooseExts]

/-- **The records and buffers after a piece's step**: the piece's record written (`pcRec`) over
its record after the allocation `ra` (its own but the sources and page id), the parent's with its
entry (`pcPar`, over its record modulo sources), the buffer `id` the written page; the view's
pages, the live nodes and the txid kept, the mark not lower, the run `id … id + count - 1` below
it. -/
theorem pcStepX_state {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStepX Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hpl : rl.nv.parent' ≠ null → rl.nv.parent' ≠ l)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl) :
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
  sorry

/-- **The spill's global state after a piece's step.** -/
theorem pcStepX_spG {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStepX Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hlv : l ∈ Xi.live) (hne : 0 < rl.ws.length)
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
    {st : List FLStep} {id : w64} (hs : pcStepX Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hd : objsDisj Xi.t)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl) :
    spFrame Xi X3 bl [l, rl.nv.parent'] := by
  sorry

/-- **A piece's step is a spill step** for the slots `O` (owned with `L`, which holds the piece's
own page, if any). -/
theorem pcStepX_step {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} {O L : List Nat} (hs : pcStepX Xi wi bl l rl count X3 w2 st id)
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
    {st : List FLStep} {id : w64} {L : List Nat} (hs : pcStepX Xi wi bl l rl count X3 w2 st id)
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
    {st : List FLStep} {id : w64} {O L : List Nat} (hs : pcStepX Xi wi bl l rl count X3 w2 st id)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl)
    (hsl : slotInv wi.fl Xi.t.mv.pgid'.toNat (O ++ (ownSl Xi.v rl.nv.pgid' ++ L))) :
    slotInv w2.fl X3.t.mv.pgid'.toNat (O ++ L ++ List.range' id.toNat count) := by
  sorry

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

end state

end Spill

end bbolt
end EtcdGrove
end Perennial
