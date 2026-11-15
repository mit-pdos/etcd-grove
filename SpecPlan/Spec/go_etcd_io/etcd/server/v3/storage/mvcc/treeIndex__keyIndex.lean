/-
`(*treeIndex).keyIndex(keyi)` (`index.go:88`), the lock held: the tree's key index of `keyi`'s key
(1g's `Get`), lent, or `nil`. Internal (`unsafeGet`, `KeyIndex`). **Changes**: over `treeOwn`.
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

/-- `ti.keyIndex(keyi)`. -/
def treeIndex.keyIndex.spec : Prop :=
  ∀ (ti : Loc) (dq : DFrac) (M : IndexM) (keyi : Loc) (k : GoString) (ki0 : KeyIndexM) (dq' : DFrac),
  {{ pkgInit ∗ treeOwn ti dq M ∗ ownKi keyi k ki0 dq' }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"keyIndex")) (Val #keyi))
  {{ (p : Loc), RET #p; ownKi keyi k ki0 dq' ∗
      ((⌜M k = none ∧ p = null⌝ ∗ treeOwn ti dq M) ∨
       (∃ ki, ⌜M k = some ki ∧ p ≠ null⌝ ∗ ownKi p k ki dq ∗ (ownKi p k ki dq -∗ treeOwn ti dq M))) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
