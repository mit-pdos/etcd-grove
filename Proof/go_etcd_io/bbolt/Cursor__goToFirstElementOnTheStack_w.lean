/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__goToFirstElementOnTheStack_w.lean` (U6z, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"). Unfinished: the loop as
`goToFirstElementOnTheStack_r`'s, over `Bucket.pageNode_w.specQ` (each child's reference fresh:
`refAt`; a node's registry fragment from `nlFrags`, F1), the child's page id read from the top
reference (a node's inode, `nodePg`'s page ids; a page's branch element), and the new leaf's
`sLeafOK` by the bridging lemma (see `Cursor__keyValue_ws`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_w

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

theorem Cursor.goToFirstElementOnTheStack_w.wp_proofQ : Cursor.goToFirstElementOnTheStack_w.specQ (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
