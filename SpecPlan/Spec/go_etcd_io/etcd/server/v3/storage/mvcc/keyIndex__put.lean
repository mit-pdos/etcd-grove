/-
`(*keyIndex).put(lg, main, sub)` (`key_index.go:80`): the revision appended to the last generation
(a first one made if none: `kiPut`). Internal (`treeIndex.Put`, `restoreIntoIndex`). The revision
above `modified` is a premise (`lg.Panic` otherwise: the store writes increasing revisions, and
`restoreIntoIndex` reads them in order). **Changes** from `specs-ref`'s file: the panic excluded by a
premise instead of a panic result; over `Internal.lean`'s model.
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

/-- `ki.put(lg, main, sub)` above `modified`. -/
def keyIndex.put.spec : Prop :=
  ∀ (p lg : Loc) (k : GoString) (ki : KeyIndexM) (main sub : w64),
  {{ pkgInit ∗ ⌜Rev.gt ⟨main, sub⟩ ki.modified = true⌝ ∗ ownKi p k ki (DFrac.own 1) }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"put")) (Val #lg))
      (Val #main)) (Val #sub))
  {{ RET #(); ownKi p k (kiPut ki ⟨main, sub⟩) (DFrac.own 1) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
