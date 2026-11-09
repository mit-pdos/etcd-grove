/-
`(*keyIndex).compact(lg, atRev, available)` (`key_index.go:215`) on a non-empty, well-formed key
index (`lg.Panic` on an empty one; `doCompact`'s premises): `kiCompact`, the kept revision added to
`available`. Internal (`treeIndex.Compact`). **Changes**: over `availAt`, premises for the panics.
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

/-- `ki.compact(lg, atRev, available)`. -/
def keyIndex.compact.spec : Prop :=
  ∀ (p lg m : Loc) (k : GoString) (ki : KeyIndexM) (atRev : w64) (A : Rev → Prop),
  {{ pkgInit ∗ ⌜ki.gens ≠ [] ∧ kiIsEmpty ki = false ∧ kiWf ki⌝ ∗ ownKi p k ki (DFrac.own 1) ∗
      availAt m A }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"compact")) (Val #lg))
      (Val #atRev)) (Val #m))
  {{ RET #(); ownKi p k (kiCompact ki atRev) (DFrac.own 1) ∗ availAt m (compactAvail A ki atRev) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
