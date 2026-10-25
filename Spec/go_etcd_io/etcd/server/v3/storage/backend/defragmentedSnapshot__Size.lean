/-
`Size` (the backend's `defragmentedSnapshot`, `backend.go`: the method its embedded `snapshot`
promotes; `etcd#21776`). `s.Size()`: the size of the defragmented temporary database the snapshot's
read transaction sees. Lean-first (no Rocq counterpart); the vocabulary is `InvSnapshot.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `s.Size()` of a share of an open defragmented snapshot: some number, the share given back
(`Size` only reads; after `Close` it would dereference the transaction's nil `meta`). -/
abbrev backend.defragmentedSnapshot.Size.spec : Prop :=
  ∀ (ds : Loc) (D : Data) (γ : GName × GName) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      defragSnapOpenQ ds D γ q }}
    (App (Val (ds @!! go.GoType.PointerType defragmentedSnapshot.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; defragSnapOpenQ ds D γ q }}

end spec

end EtcdGrove
end Perennial
