/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__prev_w.lean` (U6z, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"). Unfinished: `prev`'s upward scan (the leaf empty: up to a branch with an
index above `0`, then `last_w`; at the root, `first_w`), keeping `wLastInv` (U6y's F4).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__prev_w

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

theorem Cursor.prev_w.wp_proofQ : Cursor.prev_w.specQ (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
