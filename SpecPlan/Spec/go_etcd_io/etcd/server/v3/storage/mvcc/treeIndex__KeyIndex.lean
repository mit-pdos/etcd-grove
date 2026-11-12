/-
`(*treeIndex).KeyIndex(keyi)` (`index.go:82`) on a tree index no other goroutine reaches (its
caller, `restoreIntoIndex`'s goroutine, rebuilds a private one): the pointer to the key index of
`keyi`'s key, or `nil`. Internal. **Changes**: over `ownIdxPriv`'s pointers.
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

/-- `ti.KeyIndex(keyi)` on a private index. -/
def treeIndex.KeyIndex.spec : Prop :=
  ∀ (ti : Loc) P (keyi : Loc) (k : GoString) (ki0 : KeyIndexM) (dq : DFrac),
  {{ pkgInit ∗ ownIdxPriv ti P ∗ ownKi keyi k ki0 dq }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"KeyIndex")) (Val #keyi))
  {{ RET #(((P k).map Prod.fst).getD null); ownIdxPriv ti P ∗ ownKi keyi k ki0 dq }}

end spec
end Mvcc
end EtcdGrove
end Perennial
