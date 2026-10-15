/-
`NewHooks` (the backend). `NewHooks(f)`: a `Hooks` whose `OnPreCommitUnsafe` is `f`.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

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

/-- `NewHooks(f)`: a `Hooks` whose `OnPreCommitUnsafe` is `f`. -/
abbrev backend.NewHooks.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ hookFnSpec γ P Pk b t f }}
    (App (Val (@! NewHooks)) (Val #f))
  {{ (h : GoInterface), RET #h; hooksSpec γ P Pk b t h }}

end spec

end EtcdGrove
end Perennial
