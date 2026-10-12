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

/-- `ki.tombstone(lg, main, sub)` (a non-nil logger) on a non-empty key index with a generation:
if the last generation is empty (the key is already deleted), `ErrRevisionNotFound`, the key
index unchanged; else `nil`, with the revision appended and a new empty generation
(`kiTombstone`), possibly reallocating the generations slice. The code panics, which nothing
recovers (the call is stuck), on an empty key index (`isEmpty`, `lg.Panic`) and, past an
empty last generation, on a revision not above `modified` (`ki.put`): both are premises.

`ki.gens ≠ []` stays a premise: with no generation, `ki.generations[len-1]` is a run-time
panic (an index out of range, which Perennial models as stuck), unreachable in the verified
code (a key index in the tree always has a generation). -/
abbrev mvcc.keyIndex.tombstone.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (k : GoString) (lg : Loc) (main sub : w64)
    (e : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜lg ≠ null⌝ ∗ ⌜ki.gens ≠ []⌝ ∗ ⌜mvcc.kiIsEmpty ki = false⌝ ∗
      ⌜mvcc.kiLastEmpty ki = false → mvcc.Rev.lt ki.modified ⟨main, sub⟩⌝ ∗ mvcc.kiKey p k ∗ mvcc.ownKi p gs ki (DFrac.own 1) ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"tombstone")) (Val #lg))
      (Val #main)) (Val #sub))
  {{ (r : val), RET r;
      if mvcc.kiLastEmpty ki then
        ⌜r = #(GoInterface.ok e)⌝ ∗ mvcc.ownKi p gs ki (DFrac.own 1)
      else
        ⌜r = #GoInterface.nil⌝ ∗
          ∃ gs' : GoSlice, mvcc.ownKi p gs' (mvcc.kiTombstone ki ⟨main, sub⟩) (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
