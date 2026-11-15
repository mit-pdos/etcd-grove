/-
`(*keyIndex).isEmpty()` (`key_index.go:293`): one generation, empty (`kiIsEmpty`). A read.
Internal (`get`, `tombstone`, `compact`, `keep`, `treeIndex.Compact`). **Changes**: none.
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

/-- `ki.isEmpty()`. -/
def keyIndex.isEmpty.spec : Prop :=
  ∀ (p : Loc) (k : GoString) (ki : KeyIndexM) (dq : DFrac),
  {{ pkgInit ∗ ownKi p k ki dq }}
    (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"isEmpty")) (Val #()))
  {{ RET #(kiIsEmpty ki); ownKi p k ki dq }}

end spec
end Mvcc
end EtcdGrove
end Perennial
