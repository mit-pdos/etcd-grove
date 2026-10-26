/-
`authStore.commitRevision` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
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

/-- **`as.commitRevision(tx)`** (`atomic.AddUint64(&as.revision, 1)`, then
`tx.UnsafeSaveAuthRevision(as.Revision())`) under the batch lock's token at the pending state
`sta`, whose revision is the latest recorded state's (`st0`: the atomic holds it, `revCur`), from
the authority `hs`: the step's state `bump sta` is appended (with valid permission keys; disabled
in the mode `off`), the atomic is its revision, and the token's state has the revision written
(`revAfter`: the atomic's value plus one, which in `on γa` is the model's; in the other modes the
atomic is not tied to the model). -/
abbrev auth.authStore.commitRevision.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (ti : GoInterfaceOk) (Lk : AuthState → IProp GF → IProp GF) (sta : AuthState) (X : IProp GF)
    (hs : List AuthState) (st0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authBatchTxLk ti M P f T Lk ∗ Lk sta X ∗ authOwnF M hs ∗
      ⌜histLast M hs st0 ∧ sta.revision = st0.revision ∧ sta.revision + 1 < 2 ^ 64 ∧
        (M.isOn = true → M ≠ .any → permKeysOk sta) ∧ (M = .off → sta.enabled = false)⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"commitRevision"))
      (Val #(GoInterface.ok ti)))
  {{ RET #(); ∃ rev : Nat, ⌜revAfter M sta rev⌝ ∗ Lk { sta with revision := rev } X ∗
      authOwnF M (hs ++ [bump sta]) }}

end spec

end EtcdGrove
end Perennial
