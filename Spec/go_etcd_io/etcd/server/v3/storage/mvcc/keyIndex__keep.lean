/-
`(*keyIndex).keep(atRev, available)` (`key_index.go:238`): nothing for an empty key index; else
`doCompact`'s revision added, deleted again for a tombstone ending a generation that is not the last
(`keepAvail`). A read. Internal (`treeIndex.Keep`). **Changes**: over `availAt`.
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

/-- `ki.keep(atRev, available)`. -/
def keyIndex.keep.spec : Prop :=
  ∀ (p m : Loc) (k : GoString) (ki : KeyIndexM) (dq : DFrac) (atRev : w64) (A : Rev → Prop),
  {{ pkgInit ∗ ⌜ki.gens ≠ [] ∧ kiWf ki⌝ ∗ ownKi p k ki dq ∗ availAt m A }}
    (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"keep")) (Val #atRev)) (Val #m))
  {{ RET #(); ownKi p k ki dq ∗ availAt m (keepAvail A ki atRev) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
