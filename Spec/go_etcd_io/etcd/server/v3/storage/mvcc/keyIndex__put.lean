/-
`keyIndex.put` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `ki.put(lg, main, sub)` (a non-nil logger): with a revision above `modified`, the revision
is appended to the last generation (`kiPut`; a first generation is made if there is none),
possibly reallocating the generations slice; else `lg.Panic` panics with its message, the key
index unchanged (the check precedes every write). -/
abbrev mvcc.keyIndex.put.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (lg : Loc) (main sub : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜lg ≠ null⌝ ∗ mvcc.ownKi p gs ki (DFrac.own 1) }}
    (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"put")) (Val #lg))
      (Val #main)) (Val #sub))
  {{ (r : val), RET r;
      if mvcc.Rev.lt ki.modified ⟨main, sub⟩ then
        ⌜r = #()⌝ ∗ ∃ gs' : GoSlice, mvcc.ownKi p gs' (mvcc.kiPut ki ⟨main, sub⟩) (DFrac.own 1)
      else
        ⌜r = PanicV #(go!"'put' with an unexpected smaller revision")⌝ ∗
          mvcc.ownKi p gs ki (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
