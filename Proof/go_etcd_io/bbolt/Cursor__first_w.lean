/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__first_w.lean` (U6z, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"). Unfinished: the stack reset, `Bucket.pageNode_w.specQ` of the root
(`X.rootPid bl`), `goToFirstElementOnTheStack_w`, `next_w` on an empty first leaf, `keyValue_ws`;
position `0` by `stackPos` of a first path.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__first_w

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

theorem Cursor.first_w.wp_proofQ : Cursor.first_w.specQ (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
