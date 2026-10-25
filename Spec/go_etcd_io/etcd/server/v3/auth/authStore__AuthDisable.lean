/-
`authStore.AuthDisable` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (the
write side's contracts) and `Steps.lean` (the model's steps).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.AuthDisable()`** from the admin side's authority `hs`: having read the flag `en`
(under `enabledMu`), the step `authDisableF en` (disabled and the revision bumped, or nothing). -/
abbrev auth.authStore.AuthDisable.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ authOwn M hs ∗ authWR st M P f T ∗ tpAdmin st M ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (authDisableF en))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthDisable")) (Val #()))
  {{ RET #(); tpAdmin st M ∗ (Post ∨ Pre) ∗ authWR st M P f T ∗
      ∃ en : Bool, enabledVerdict M en ∗ adminOut M hs (stepOf (authDisableF en)) noExtra GoInterface.nil }}

end spec

end EtcdGrove
end Perennial
