/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__next_w.lean` (U6z, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"). Unfinished: `next`'s loop (the upward scan over `count()`
of each reference, stale-tolerant as in `keyValue_ws`; `stackPos_nextR` for the positions), then
`goToFirstElementOnTheStack_w`, the empty-leaf restart, and `keyValue_ws`; `next_we`: the scan finds
no level (every branch last, the leaf at or past its last index).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_w

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.next_w.wp_proofQ : Cursor.next_w.specQ (GF := GF) (hG := hG) := by
  sorry

theorem Cursor.next_we.wp_proofQ : Cursor.next_we.specQ (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
