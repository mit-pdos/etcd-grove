/-
`authStore.Close` (`server/auth/store.go`): the server's `Cleanup` closes the auth store (R2b-3c
part 2, 2026-11-04). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.Close()`**, with the token provider's admin resource (`tpAdmin`, which `AuthDisable` also
takes): under `enabledMu`, if auth is enabled, the token provider's `disable()`; it returns `nil`.
The model's state is unchanged (the flag is only read). -/
abbrev auth.authStore.Close.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      tpAdmin st M }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ tpAdmin st M }}

end spec

end EtcdGrove
end Perennial
