/-
The writer's records right after `beginRWTx` (U5 of `notes/bbolt-proof-plan.md`; design §3.13):
`wx0`, the root bucket at `txRoot tx` without root node or caches, on the committed state's view.
Its pure facts: `wOK`, its data the committed data (`wtxData_wx0`), `gensOK`, and the freelist
facts `flViewU` asks of it.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Fuel
public import Proof.go_etcd_io.bbolt.Read.BktOK
public import Proof.go_etcd_io.bbolt.Inv.MatReady
public import Proof.go_etcd_io.bbolt.Txn.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section winit
variable [GooseExts]

/-- The root bucket's record right after `Tx.init`: no root node, empty caches. -/
def brec0 (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) : BRec :=
  ⟨bv, ib, ∅, ∅, ∅, [], Src.own DFrac.discard, PageSt.none⟩

/-- **The writer's records right after `Tx.init`** (and `db.rwtx = t`): the root bucket at `rl`
without root node or caches, nothing else. -/
def wx0 (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) : WX :=
  { t := { t := t, mv := mv, pm := ∅, bufs := ∅, bs := GMap.singleton rl (brec0 bv ib),
           dead := ∅, deadB := ∅ },
    live := ∅, liveB := GMap.singleton rl (), handles := ∅, nloc := ∅, v := v, rl := rl }

/-- What `Tx.init` leaves for a writer (pure): writable, the meta copy one txid on and the
committed state's high-water mark, the root bucket's header at the committed root, no root node,
no page. -/
structure Init0 (C : CommitSt) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket)
    (ib : InBucket) : Prop where
  writable : t.writable' = true
  txid : mv.txid'.toNat = C.txid + 1
  pgid : mv.pgid'.toNat = C.hwm
  root : ib.root' = W64 (C.root : Int)
  rootNode : bv.rootNode' = null
  page : bv.page' = null

theorem treeOK_root (C : CommitSt) (htree : treeOK C) : 2 ≤ C.root ∧ C.root < C.hwm := by
  obtain ⟨⟨hwf, -⟩, -⟩ := htree
  cases hwf with
  | page _ _ h2 hlt _ _ _ _ => exact ⟨h2, hlt⟩

theorem wx0_bs (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) (bl : Loc) :
    (wx0 rl t mv bv ib v).t.bs !! bl = if rl = bl then some (brec0 bv ib) else none := by
  simp [wx0]

theorem wx0_bs_some (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket)
    (v : View) (bl : Loc) (B : BRec) (h : (wx0 rl t mv bv ib v).t.bs !! bl = some B) :
    bl = rl ∧ B = brec0 bv ib := by
  rw [wx0_bs] at h
  split at h
  · cases h; rename_i h; exact ⟨h.symm, rfl⟩
  · cases h

/-- **The initial records are well-formed.** -/
theorem wOK_wx0 (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket)
    (ib : InBucket) (htree : treeOK C) (hi : Init0 C t mv bv ib) :
    wOK (wx0 rl t mv bv ib (View.ofC b C)) := by
  obtain ⟨h2, hlt⟩ := treeOK_root C htree
  have hhwm : C.hwm < 2 ^ 64 := by have := hi.pgid; rw [← this]; exact BitVec.isLt _
  have hr64 : C.root < 2 ^ 64 := by omega
  have hrt : ib.root'.toNat = C.root := by rw [hi.root]; exact toNat_W64_of_lt _ hr64
  have hr0 : ib.root' ≠ W64 0 := by
    intro e; rw [e] at hrt; simp at hrt; omega
  have hbs := wx0_bs_some rl t mv bv ib (View.ofC b C)
  have hrt' : (brec0 bv ib).ib.root'.toNat = C.root := hrt
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hi.writable
  · rfl
  · show 2 ≤ mv.pgid'.toNat; rw [hi.pgid]; omega
  · show C.txid + 1 = mv.txid'.toNat; rw [hi.txid]
  · simp [wx0]
  · intro bl B hB
    obtain ⟨rfl, rfl⟩ := hbs bl B hB
    refine ⟨?_, fun name c h => by simp [brec0] at h⟩
    show bktClean (View.ofC b C) mv.pgid'.toNat bl (brec0 bv ib)
    rw [hi.pgid]
    refine ⟨fun h => absurd h hr0, fun _ => ⟨by rw [hrt']; exact hlt, fun _ => by
      rw [hrt']; exact htree.1.1⟩, fun _ => ⟨rfl, rfl⟩, fun h => absurd hi.rootNode h,
      fun c l h => by simp [brec0] at h, fun _ => hi.page, fun h => absurd h hr0,
      fun l r h => by simp [brec0] at h, ?_, ?_⟩
    · intro l1 i1 c1 l2 i2 c2 h1
      obtain ⟨r, -, h, -⟩ := h1; simp [brec0] at h
    · intro l i c h1
      obtain ⟨r, -, h, -⟩ := h1; simp [brec0] at h
  · intro bl B hB
    obtain ⟨rfl, rfl⟩ := hbs bl B hB
    refine ⟨⟨fun _ => (none, none), fun _ _ => by rw [hrt']; exact htree.1.2.2.1,
      fun r h => by simp [brec0] at h, fun l r h => by simp [brec0] at h⟩, ?_⟩
    intro k c h; simp [brec0] at h
  · intro bl B hB l r h
    obtain ⟨rfl, rfl⟩ := hbs bl B hB; simp [brec0] at h
  · intro bl B hB l r h
    obtain ⟨rfl, rfl⟩ := hbs bl B hB; simp [brec0] at h
  · intro b' nm h; simp [wx0] at h
  · refine ⟨by simp [wx0, Membership.mem], fun l h => by simp [wx0, Membership.mem] at h, ?_,
      fun bl B l r hB h => by obtain ⟨rfl, rfl⟩ := hbs bl B hB; simp [brec0] at h,
      fun l h => by simp [wx0] at h⟩
    intro bl B hB
    obtain ⟨rfl, rfl⟩ := hbs bl B hB
    simp [wx0, Membership.mem]
  · intro n b' p h; simp [wx0] at h
  · exact ⟨C, htree, rfl⟩

/-- **The initial records' generations**: no handle, no opened bucket. -/
theorem gensOK_wx0 (T : TxView) (rl : Loc) (t : Tx) (mv : Meta) (bv : go_etcd_io.bbolt.Bucket)
    (ib : InBucket) (v : View) : gensOK T (wx0 rl t mv bv ib v) := by
  refine ⟨fun b n g h => by simp [wx0] at h, fun n b' h => ?_⟩
  simp [bktLoc, wx0, brec0] at h

/-- `Tx.init`'s writer meta: one txid on, the committed state's high-water mark and root. -/
theorem initMeta_facts (C : CommitSt) (hok : C.metaOk) (h64 : C.txid + 1 < 2 ^ 64) :
    (initMeta true (metaOf (C.slot C.txid))).txid'.toNat = C.txid + 1 ∧
    (initMeta true (metaOf (C.slot C.txid))).pgid'.toNat = C.hwm ∧
    (metaOf (C.slot C.txid)).root'.root' = W64 (C.root : Int) := by
  obtain ⟨-, -, -, -, -, -, ⟨htx, hr, hpg, -⟩, -⟩ := hok
  refine ⟨?_, ?_, ?_⟩
  · simp only [initMeta, ↓reduceIte]
    rw [BitVec.toNat_add, htx]; simp; omega
  · simp only [initMeta, ↓reduceIte]; exact hpg
  · apply BitVec.eq_of_toNat_eq; rw [hr]
    have := (metaOf (C.slot C.txid)).root'.root'.isLt
    rw [hr] at this
    simp; omega

/-- **An idle writer side has no pending entry for the next writer** (`flBelow` without a live
writer: every pending transaction is committed). -/
theorem pending_next_none (fl : FLPg) (C : CommitSt) (h : flBelow fl C none) :
    fl.pending !! W64 ((C.txid + 1 : Nat) : Int) = none := by
  cases hp : fl.pending !! W64 ((C.txid + 1 : Nat) : Int) with
  | none => rfl
  | some pd =>
    rcases h.2.2.1 _ pd hp with hle | ⟨hw, -⟩
    · rw [toNat_W64_of_lt _ h.2.2.2.1] at hle; omega
    · cases hw

end winit

end bbolt
end EtcdGrove
end Perennial
