/-
**What a remap inside `allocate` keeps of the writer's records** (the coordinator's addition (1) to
batch 44.1, U10i's need: `commitFreelist`'s second rollback entailment): the transaction's struct
`X.t.t` (so its `writable` flag) and, of every bucket's record, everything but its nodes and its
inline page's source (`BRec.unview` and `bktStep` change only `ns`, `isrc`, `pst`): its `bv`, `ib`,
`nm`, `bm`. `X'.t.bs = X.t.bs` itself is false (`dereference` copies the nodes' keys and values,
`WX.rebase` marks view sources stale).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rrec
variable [GooseExts]

/-- A bucket record's fields that no remap changes. -/
def BRec.fixed (B : BRec) : Bucket × InBucket × GMap w64 Loc × GMap GoString Loc :=
  (B.bv, B.ib, B.nm, B.bm)

theorem bktStep_fixed (B B' : BRec) (h : bktStep B B') : B'.fixed = B.fixed := by
  have e := h.1
  unfold BRec.fixed
  rw [← e]

theorem BRec.unview_fixed (B : BRec) : B.unview.fixed = B.fixed := rfl

/-- **A remap keeps the transaction's struct** (`derefStep`'s `t`; `WX.rebase` keeps it). -/
theorem derefRel_rebase_tt (X Xd : WX) (b : Loc) (h : derefRel X Xd) :
    (Xd.rebase b).t.t = X.t.t :=
  (h.2.2.2.2.2.2.2.2.2.2.2.2.2).2.2.2.2.2.1

/-- **A remap keeps every bucket record's fixed fields** (`bv`, `ib`, `nm`, `bm`), and which
buckets have a record. -/
theorem derefRel_rebase_bs (X Xd : WX) (b : Loc) (h : derefRel X Xd) (bl : Loc) :
    ((Xd.rebase b).t.bs !! bl).map BRec.fixed = (X.t.bs !! bl).map BRec.fixed := by
  have hs := (h.2.2.2.2.2.2.2.2.2.2.2.2.2).2.2.2.2.2.2.2.2.2.2.2.2 bl
  show ((Xd.t.bs.fmap BRec.unview) !! bl).map BRec.fixed = _
  rw [GMap.lookup_fmap]
  revert hs
  cases X.t.bs !! bl <;> cases Xd.t.bs !! bl <;> simp [optRel]
  intro hB
  rw [BRec.unview_fixed, bktStep_fixed _ _ hB]

/-- The root bucket's record survives a remap, with its children map. -/
theorem derefRel_rebase_root (X Xd : WX) (b : Loc) (h : derefRel X Xd) :
    ((Xd.rebase b).t.bs !! X.rl).isSome = (X.t.bs !! X.rl).isSome ∧
      ((Xd.rebase b).t.bs !! X.rl).map BRec.bm = (X.t.bs !! X.rl).map BRec.bm := by
  have e := derefRel_rebase_bs X Xd b h X.rl
  constructor
  · have := congrArg Option.isSome e
    simpa using this
  · have := congrArg (Option.map fun x => x.2.2.2) e
    simpa [Option.map_map, Function.comp_def, BRec.fixed] using this

end rrec

end bbolt
end EtcdGrove
end Perennial
