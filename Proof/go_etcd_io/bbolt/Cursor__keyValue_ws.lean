/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__keyValue_ws.lean` (U6z, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"). Unfinished: as `Cursor.keyValue_w`'s proof (its callees: `Page.Count`,
`LeafPageElement`, the leaf element's and inode's `Key`/`Value`/`Flags`), but the top reference is
read through the cursor's persistent part: a node reference by its registry fragment (`nlAuth`'s
auth, `nlocCur`: the live node of its position), a page reference at `pageLoc` (the view's cells) or
the inline root page (`wInlOwn`); the leaf's entries are `entsIn es (pathBnd …)` (`sLeafOK` for a
page; for a node, the bridging lemma: the leaf a base path reaches is a walk leaf whose bounds are
`pathBnd`, by `nodePg`'s keys, F3, and `ltree_leaf_of_T'`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__keyValue_ws

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

theorem Cursor.keyValue_ws.wp_proofQ : Cursor.keyValue_ws.specQ (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
