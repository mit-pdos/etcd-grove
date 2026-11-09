/-
`(*treeIndex).unsafeGet(key, atRev)` (`index.go:74`), the lock held: `keyIndex` then `get`
(`idxGetRes`; its key indexes non-empty, `get`'s panic otherwise). Internal (`Get`, `Revisions`,
`CountRevisions`, `Range`). **Changes**: over `treeOwn`.
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

/-- `ti.unsafeGet(key, atRev)`. -/
def treeIndex.unsafeGet.spec : Prop :=
  ∀ (ti : Loc) (dq : DFrac) (M : IndexM) (key : GoSlice) (k : GoString) (dk : DFrac) (atRev : w64)
    (e : GoInterface),
  {{ pkgInit ∗ treeOwn ti dq M ∗ ⌜idxNonEmpty M⌝ ∗ key ↦*{dk} k ∗
      globalAddr ErrRevisionNotFound ↦□ e }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"unsafeGet")) (Val #key)) (Val #atRev))
  {{ (r : val), RET r; treeOwn ti dq M ∗ key ↦*{dk} k ∗ ⌜r = getVal (idxGetRes M k atRev) e⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
