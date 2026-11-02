/-
**`IsAdminPermitted` no older than a reader's lower bound** (the lease-src plan, 2026-11-02;
`notes/lease-src-plan.md`). Lean-first (no Rocq counterpart).

As `IsAuthEnabled.specLb` and the permission checks' `specLb`s (E3h, E3j): a reader holding a lower
bound `n` of the published index (`authPubLbM`) has `IsAdminPermitted`'s passing verdict at a state
no older than `n`. `IsAdminPermitted` passes when `IsAuthEnabled()` reads `false` (a state no
older than `n`, `IsAuthEnabled.specLb`), or when the user its read transaction finds (a state no
older than `n`, `lockedReadTx.specLb`) has the root role; either way `adminOk` holds of that state.
What the lease checks need of it (`isAuthStoreLeaseLb`). A refusal is stated by nothing here (the
lease checks need only the passing verdict).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Fresh
public import Proof.go_etcd_io.etcd.server.v3.auth.ReadLb
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAdminPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section defs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **`IsAdminPermitted`'s verdict no older than the index `n`** in the mode `M` (persistent): in
`on γa`, a pass admits the principal (`adminOk`) at a state recorded at an index at least `n`; in
`off`, it passes; in `any`, nothing. -/
def adminVerdictFrom (M : AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa => iprop(∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
      ⌜n ≤ i ∧ (err = GoInterface.nil → adminOk st (some (authInfoM info)))⌝)

instance adminVerdictFrom_persistent (M : AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    Persistent (adminVerdictFrom (GF := GF) M n info err) := by
  unfold adminVerdictFrom; cases M <;> infer_instance

end defs

end auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.IsAdminPermitted(authInfo)` read by a reader with the lower bound `n`, for a non-nil
`authInfo`: the verdict at a state no older than `n` (`adminVerdictFrom`). -/
abbrev auth.authStore.IsAdminPermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (a : Loc) (info : AuthInfo)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ authPubLbM M n }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAdminPermitted")) (Val #a))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ authErrIs err ∗
      auth.adminVerdictFrom M n info err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.IsAdminPermitted.wp_lb
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (h_lockedReadTx : auth.authStore.lockedReadTx.specLb (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsAdminPermitted.specLb (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
