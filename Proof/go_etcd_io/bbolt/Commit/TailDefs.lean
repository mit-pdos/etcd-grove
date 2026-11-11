/-
**`Commit`'s tail** (U10j of `notes/bbolt-proof-plan.md`): what holds where the freelist's branches
(`commitFreelist`, `NoFreelistSync`'s `SetFreelist`) join, before `grow`, `write`, `writeMeta` and
`close`: the records `X` and the writer side `w` (pure facts here; the resources are `wtxW`,
`wdbW`, `cmExcl` and the full database).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.AssembleEnd
public import Proof.go_etcd_io.bbolt.Commit.TailPub
public import Proof.go_etcd_io.bbolt.Inv.WdbFlag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- **The tail's facts** of the records `X` and the writer side `w` (flagged `fr`: after the free
of the synced freelist page), `opg` the high-water mark before the spill (`Commit`'s `opgid`):
`wtxEnd`'s facts and `rollback`'s txid, the mark inside the mapping, the committed one `opg`, no
commit handler, the committed state without a synced freelist page unless it was freed (`fr`),
the writer side's facts `wdbOK' fr`, the committed state holding the transaction's base data `Db`
(`T.base`), and the publish's facts for its data `D` (`T.cur`, `cmPubPre`). -/
def cmTailOK (fr : Bool) (D Db : Data) (X : WX) (w : WDb) (opg : w64) : Prop :=
  X.t.t.writable' = true ∧ (X.t.bs !! X.rl).isSome ∧ X.t.mv.txid' = w.wtxid ∧
  X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms ∧ w.C.hwm = opg.toNat ∧
  X.t.t.commitHandlers' = slice.nil ∧ (X.t.t.meta' ≠ null ∧ 0 < X.t.t.meta'.addr) ∧
  (fr = false → w.C.flpg = none) ∧
  wdbOK' fr w ∧ Db = treeData w.C ∧ cmPubPre D X w

end pure

end bbolt
end EtcdGrove
end Perennial
