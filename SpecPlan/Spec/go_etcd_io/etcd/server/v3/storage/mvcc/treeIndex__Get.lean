/-
`(*treeIndex).Get(key, atRev)` (`index.go:68`): under the read lock, `unsafeGet`; by the caller's
update, unchanged, at a revision at least the floor (`idxGetRes`). Internal (`storeTxnWrite.put`).
**Changes**: an atomic update over `idxAt`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

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

/-- `ti.Get(key, atRev)`. -/
def treeIndex.Get.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (key : GoSlice) (k : GoString) (dk : DFrac) (atRev : w64)
    (e : GoInterface) (Q : IndexM → IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      key ↦*{dk} k ∗ globalAddr ErrRevisionNotFound ↦□ e ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗ ⌜c ≤ sint.Z atRev⌝ }> @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi M c, COMM Q M }> }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Get")) (Val #key)) (Val #atRev))
  {{ (r : val), RET r; key ↦*{dk} k ∗ ∃ M : IndexM, Q M ∗ ⌜r = getVal (idxGetRes M k atRev) e⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
