/-
`Close` (the backend's `defragmentedSnapshot`, `backend.go`; `etcd#21776`). `s.Close()`: defers
`s.closer()` (closing and removing the temporary defragmented database), closes the embedded
`s.snapshot` (stopping the warning goroutine and rolling back the read transaction on the temporary
database), and then runs the deferred `s.closer()`. Lean-first (no Rocq counterpart); the vocabulary
is `InvSnapshot.lean`.
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

/-- `s.Close()` of an open defragmented snapshot, the whole of it (no share left to read it after):
closed (`defragSnapOpenQ` consumed), with a nil error. -/
abbrev backend.defragmentedSnapshot.Close.spec : Prop :=
  ∀ (ds : Loc) (D : Data) (γ : GName × GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      defragSnapOpenQ ds D γ 1 }}
    (App (Val (ds @!! go.GoType.PointerType defragmentedSnapshot.ty @!! go!"Close")) (Val #()))
  {{ RET #GoInterface.nil; True }}

end spec

end EtcdGrove
end Perennial
