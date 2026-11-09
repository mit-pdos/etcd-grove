/-
`(*keyIndex).tombstone(lg, main, sub)` (`key_index.go:131`) on a non-empty key index with a
generation (`lg.Panic` on an empty one; an index out of range with none): `ErrRevisionNotFound` if
the last generation is empty, else a put and a new empty generation (`kiTombstone`; the revision
above `modified`, `put`'s panic otherwise). Internal (`treeIndex.Tombstone`, `restoreIntoIndex`).
**Changes**: the panics excluded by premises.
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

/-- `ki.tombstone(lg, main, sub)`. -/
def keyIndex.tombstone.spec : Prop :=
  ∀ (p lg : Loc) (k : GoString) (ki : KeyIndexM) (main sub : w64) (e : GoInterface),
  {{ pkgInit ∗ ⌜ki.gens ≠ [] ∧ kiIsEmpty ki = false ∧
        (kiLastEmpty ki = false → Rev.gt ⟨main, sub⟩ ki.modified = true)⌝ ∗
      ownKi p k ki (DFrac.own 1) ∗ globalAddr ErrRevisionNotFound ↦□ e }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"tombstone")) (Val #lg))
      (Val #main)) (Val #sub))
  {{ (err : GoInterface), RET #err;
      match kiTombstone ki ⟨main, sub⟩ with
      | none => ⌜err = e⌝ ∗ ownKi p k ki (DFrac.own 1)
      | some ki' => ⌜err = GoInterface.nil⌝ ∗ ownKi p k ki' (DFrac.own 1) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
