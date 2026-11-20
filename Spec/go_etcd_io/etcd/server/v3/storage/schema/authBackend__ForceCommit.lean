/-
`(*authBackend).ForceCommit()` (`auth.go`): `abe.be.ForceCommit()`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An `authBackend` over the backend `bi`: one call of `bi`, `ForceCommit()`: given its triple from `R`
to `Q`, it goes from `R` to `Q`. -/
abbrev schema.authBackend.ForceCommit.spec : Prop :=
  ∀ (abe : Loc) (bi : GoInterfaceOk) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abeF go!"be" abe ↦□ (GoInterface.ok bi : GoInterface) ∗ R ∗
      {{ R }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #())) {{ RET #(); Q }} }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"ForceCommit")) (Val #()))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
