/-
`(*treeIndex).Keep(rev)` (`index.go:230`): under the read lock, the revisions a compaction at `rev`
keeps (`idxKeep`), in a fresh map, by the caller's update, unchanged. Internal (`hashByRev`).
**Changes**: an atomic update over `idxAt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `ti.Keep(rev)`. -/
def treeIndex.Keep.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (rev : w64) (Q : IndexM → IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗ ⌜c ≤ sint.Z rev⌝ }> @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi M c, COMM Q M }> }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Keep")) (Val #rev))
  {{ (m : Loc), RET #m; ∃ M : IndexM, Q M ∗ availAt m (idxKeep M rev) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
