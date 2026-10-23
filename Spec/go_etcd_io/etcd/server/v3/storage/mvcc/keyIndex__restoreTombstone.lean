/-
`keyIndex.restoreTombstone` (`key_index.go`; translated 2026-10-23, the restore plan's R0).
Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `ki.restoreTombstone(lg, main, sub)` (a non-nil logger): on a key index with no generation,
`ki.restore(lg, Revision{}, Revision{main, sub}, 1)` and then a new empty generation
(`kiRestoreTombstone`); on one with generations `restore`'s panic, the key index unchanged. -/
abbrev mvcc.keyIndex.restoreTombstone.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (lg : Loc) (main sub : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜lg ≠ null⌝ ∗ mvcc.ownKi p gs ki (DFrac.own 1) }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"restoreTombstone"))
      (Val #lg)) (Val #main)) (Val #sub))
  {{ (r : val), RET r;
      if ki.gens = [] then
        ⌜r = #()⌝ ∗ ∃ gs' : GoSlice,
          mvcc.ownKi p gs' (mvcc.kiRestoreTombstone ⟨main, sub⟩) (DFrac.own 1)
      else
        ⌜r = PanicV #(go!"'restore' got an unexpected non-empty generations")⌝ ∗
          mvcc.ownKi p gs ki (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
