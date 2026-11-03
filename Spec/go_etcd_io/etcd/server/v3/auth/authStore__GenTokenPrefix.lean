/-
`authStore.GenTokenPrefix` (`server/auth/store.go`): the token provider's prefix (C1's A4,
2026-10-29). Lean-first (no Rocq counterpart).
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

/-- **`as.GenTokenPrefix()`** (`as.tokenProvider.genTokenPrefix()`): a prefix with no space
(`tokPrefixOk`) and no error, the provider's (`tokenProviderOk`'s `genTokenPrefix` clause). -/
abbrev auth.authStore.GenTokenPrefix.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"GenTokenPrefix")) (Val #()))
  {{ (s : GoString) (err : GoInterface), RET (PairV #s #err);
      ⌜err = GoInterface.nil ∧ tokPrefixOk s⌝ }}

end spec

end EtcdGrove
end Perennial
