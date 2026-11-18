/-
`(*authBackend).ForceCommit()` (`auth.go`): the backend's `ForceCommit`.
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ForceCommit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- An `authBackend` over the real backend `b`: as `backend.ForceCommit.spec`. -/
abbrev schema.authBackend.ForceCommit.spec : Prop :=
  ∀ (abe : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp) (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      schema.abeF go!"be" abe ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b : GoInterface) ∗
      isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ X ∗ commitReq γ P Pk b X Y }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"ForceCommit")) (Val #()))
  {{ RET #(); bOpen γ qo ∗ Y }}

end spec

end EtcdGrove
end Perennial
