/-
`generation.isEmpty` (`key_index.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `g.isEmpty()`: true of a nil `g`; else whether it has no revision (a read, at any
fraction). -/
abbrev mvcc.generation.isEmpty.spec : Prop :=
  (∀ (g : Loc), g = null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
      (App (Val (g @!! go.GoType.PointerType generation.ty @!! go!"isEmpty")) (Val #()))
    {{ RET #true; True }}) ∧
  (∀ (g : Loc) (gv : generation) (gm : mvcc.Gen) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        ⌜g ≠ null⌝ ∗ g ↦{dq} gv ∗ mvcc.ownGen gv gm dq }}
      (App (Val (g @!! go.GoType.PointerType generation.ty @!! go!"isEmpty")) (Val #()))
    {{ RET #(decide (gm.revs = [])); g ↦{dq} gv ∗ mvcc.ownGen gv gm dq }})

end spec

end EtcdGrove
end Perennial
