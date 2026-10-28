/-
`authStore.setRevision` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.setRevision(rev)`** (`atomic.StoreUint64`) from the authority `hs`, appending the
states `opt` (none, or one: `Recover`'s new state; `AuthEnable` appends its state before and
passes none) whose latest state's revision is `rev`: the atomic holds the latest state's revision
again. -/
abbrev auth.authStore.setRevision.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (rev : w64) (hs opt : List AuthState) (stl : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authOwnF M hs ∗
      ⌜histLast M (hs ++ opt) stl ∧ uint.nat rev = stl.revision ∧ opt.length ≤ 1 ∧
        (∀ x ∈ opt, (M.isOn = true → M ≠ .any → permKeysOk x) ∧ (M = .off → x.enabled = false))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"setRevision")) (Val #rev))
  {{ RET #(); authOwnF M (hs ++ opt) }}

end spec

end EtcdGrove
end Perennial
