/-
`keyIndex.tombstone` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `ki.tombstone(lg, main, sub)` on a key index with a generation that is not empty (else
the code panics) and a revision above `modified`: `ErrRevisionNotFound` if the last generation
is empty (the key is already deleted), else `nil` with the revision appended and a new empty
generation (`kiTombstone`), possibly reallocating the generations slice. -/
abbrev mvcc.keyIndex.tombstone.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (lg : Loc) (main sub : w64)
    (e : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜ki.gens ≠ [] ∧ mvcc.kiIsEmpty ki = false ∧ mvcc.Rev.lt ki.modified ⟨main, sub⟩⌝ ∗
      mvcc.ownKi p gs ki (DFrac.own 1) ∗ globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"tombstone")) (Val #lg))
      (Val #main)) (Val #sub))
  {{ (err : GoInterface), RET #err;
      if mvcc.kiLastEmpty ki then ⌜err = GoInterface.ok e⌝ ∗ mvcc.ownKi p gs ki (DFrac.own 1)
      else ⌜err = GoInterface.nil⌝ ∗
        ∃ gs' : GoSlice, mvcc.ownKi p gs' (mvcc.kiTombstone ki ⟨main, sub⟩) (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
