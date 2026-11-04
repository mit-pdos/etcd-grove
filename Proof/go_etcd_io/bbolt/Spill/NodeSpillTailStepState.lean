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

/-- **The allocated run is no owned slot.** -/
theorem pcStepX_fresh {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} {L : List Nat} (hs : pcStepX Xi wi bl l rl count X3 w2 st id)
    (hsl : slotInv wi.fl Xi.t.mv.pgid'.toNat L) :
    ∀ s ∈ L, s < id.toNat ∨ id.toNat + count ≤ s := by
  sorry

/-- The spill's page map after a buffer `id` is (re)written, the view's pages kept. -/
theorem spP_bufs_insert {X X' : WX} {id : w64} {pg : List w8}
    (hb : X'.t.bufs = X.t.bufs.insert id pg) (hv : X'.v.pages = X.v.pages) :
    spP X' !! id.toNat = some pg ∧ ∀ y, y ≠ id.toNat → spP X' !! y = spP X !! y := by
  sorry

end state

end Spill

end bbolt
end EtcdGrove
end Perennial
