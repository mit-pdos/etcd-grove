/-
`(*keyIndex).Less(bki)` (`key_index.go:323`): `bytes.Compare(ki.key, bki.key) == -1`: the B-tree's
order (1g's `BTree.ItemOrder`). Internal. **Changes**: over `ownKi`.
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

/-- `ki.Less(bki)`. -/
def keyIndex.Less.spec : Prop :=
  ∀ (p q : Loc) (k k' : GoString) (ki ki' : KeyIndexM) (dq dq' : DFrac),
  {{ pkgInit ∗ ownKi p k ki dq ∗ ownKi q k' ki' dq' }}
    (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"Less")) (Val #q))
  {{ RET #(decide (go.GoStringLt k k')); ownKi p k ki dq ∗ ownKi q k' ki' dq' }}

end spec
end Mvcc
end EtcdGrove
end Perennial
