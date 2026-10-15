/-
`RUnlock` (the backend). `rt.RUnlock()` of the shared read transaction: the reader's token back.
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

/-- `rt.RUnlock()` of the shared read transaction: the reader's token back. -/
abbrev backend.readTx.RUnlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (rt : Loc) (rtx : Loc) (rv : RView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ rtHeld γ P b rtx rv }}
    (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RUnlock")) (Val #()))
  {{ RET #(); rdTok γ P b }}

end spec

end EtcdGrove
end Perennial
