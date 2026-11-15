/-
`(*keyIndex).restoreTombstone(lg, main, sub)` (`key_index.go:122`) on a key index with no
generation (`restore`'s panic otherwise): `restore` at version 1, then an empty generation
(`kiRestoreTombstone`). Internal (`restoreIntoIndex`). **Changes**: the panic excluded by a premise.
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

/-- `ki.restoreTombstone(lg, main, sub)` on a key index with no generation. -/
def keyIndex.restoreTombstone.spec : Prop :=
  ∀ (p lg : Loc) (k : GoString) (ki : KeyIndexM) (main sub : w64),
  {{ pkgInit ∗ ⌜ki.gens = []⌝ ∗ ownKi p k ki (DFrac.own 1) }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"restoreTombstone"))
      (Val #lg)) (Val #main)) (Val #sub))
  {{ RET #(); ownKi p k (kiRestoreTombstone ⟨main, sub⟩) (DFrac.own 1) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
