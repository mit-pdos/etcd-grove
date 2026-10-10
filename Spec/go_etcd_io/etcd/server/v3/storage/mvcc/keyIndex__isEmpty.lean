/-
`keyIndex.isEmpty` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `ki.isEmpty()`: one generation, with no revision (`kiIsEmpty`). A read, at any fraction. -/
abbrev mvcc.keyIndex.isEmpty.spec : Prop :=
  ∀ (p : Loc) (gs : GoSlice) (ki : mvcc.KeyIndex) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownKi p gs ki dq }}
    (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"isEmpty")) (Val #()))
  {{ RET #(mvcc.kiIsEmpty ki); mvcc.ownKi p gs ki dq }}

end spec

end EtcdGrove
end Perennial
