/-
`markCov` (decision D-K of `notes/bbolt-spec-decisions.md`, maintainer 13): every slot from the
committed high-water mark to the records' mark is a dirty page's. Moved here from `Commit/TailPub`
(U10l's definition) so that `Bucket.spill.spec` (and `Tx.commitFreelist.spec`) can state it.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


section pure
variable [GooseExts]

/-- **Every slot from `hwm` to the records' mark is a dirty page's** (D-K: the mark moves only by
`allocate`'s runs, which stay in `tx.pages` until `tx.write`; so after the write the file reaches
the new mark). -/
def markCov (X : WX) (hwm : Nat) : Prop :=
  ∀ s, hwm ≤ s → s < X.t.mv.pgid'.toNat → s ∈ bufSlots X.t.bufs

/-- `markCov` holds while the mark is the committed one. -/
theorem markCov_of_eq (X : WX) (hwm : Nat) (h : X.t.mv.pgid'.toNat = hwm) : markCov X hwm := by
  intro s h1 h2; omega

end pure

end bbolt
end EtcdGrove
end Perennial
