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

/-- `ki.tombstone(lg, main, sub)` (a non-nil logger) on a key index with a generation, in the
code's order: if the key index is empty (`isEmpty`), `lg.Panic` panics with its message; if
the last generation is empty (the key is already deleted), `ErrRevisionNotFound`; if the
revision is not above `modified`, `ki.put` panics with its message; all three with the key
index unchanged. Else `nil`, with the revision appended and a new empty generation
(`kiTombstone`), possibly reallocating the generations slice.

`ki.gens ≠ []` stays a premise: with no generation, `ki.generations[len-1]` is a run-time
panic (an index out of range, which Perennial models as stuck), unreachable in the verified
code (a key index in the tree always has a generation). -/
abbrev mvcc.keyIndex.tombstone.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (k : GoString) (lg : Loc) (main sub : w64)
    (e : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜lg ≠ null⌝ ∗ ⌜ki.gens ≠ []⌝ ∗ mvcc.kiKey p k ∗ mvcc.ownKi p gs ki (DFrac.own 1) ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"tombstone")) (Val #lg))
      (Val #main)) (Val #sub))
  {{ (r : val), RET r;
      if mvcc.kiIsEmpty ki then
        ⌜r = PanicV #(go!"'tombstone' got an unexpected empty keyIndex")⌝ ∗
          mvcc.ownKi p gs ki (DFrac.own 1)
      else if mvcc.kiLastEmpty ki then
        ⌜r = #(GoInterface.ok e)⌝ ∗ mvcc.ownKi p gs ki (DFrac.own 1)
      else if mvcc.Rev.lt ki.modified ⟨main, sub⟩ then
        ⌜r = #GoInterface.nil⌝ ∗
          ∃ gs' : GoSlice, mvcc.ownKi p gs' (mvcc.kiTombstone ki ⟨main, sub⟩) (DFrac.own 1)
      else
        ⌜r = PanicV #(go!"'put' with an unexpected smaller revision")⌝ ∗
          mvcc.ownKi p gs ki (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
