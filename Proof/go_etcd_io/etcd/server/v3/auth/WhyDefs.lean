/-
**Why a request was refused: the auth store's vocabulary** (auth-guard-completeness G0/G1,
2026-11-14; `notes/auth-guard-scope.md`, §2.1-2.2). Lean-first (no Rocq counterpart).

The reasons a refusal of the auth store's checks names, each at states recorded at indices at least a
reader's lower bound `n` of the published index (`authPubLbM`; without the bound a refusal could
cite the boot state, in which auth is disabled and no user exists):

* `noPrincipalFrom`: the request side gave no principal: no token in the context, or auth disabled
  at such a state (`AuthInfoFromCtx.specLb`, `FreshCtx.lean`);
* `tokRefusedFrom`: the context's token was refused (until token liveness, the Scope's G5, only that
  there was one);
* `adminRefusedFrom`, `adminErrOf`, `adminVerdictFromO`: `IsAdminPermitted`'s refusal, with its error
  (`IsAdminPermitted.specLbO`, `FreshAdmin.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Fresh

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

namespace auth

section defs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **No principal from the request side, seen with the lower bound `n`** (persistent): the context
carries no token, or auth was disabled at a state recorded at an index at least `n` (the store's own
flag read; the disable race). -/
def noPrincipalFrom (M : AuthMode) (n : Nat) (ctx : GoInterface) : IProp GF :=
  iprop(⌜ctxTokenOf ctx = none⌝ ∨ enabledVerdictFrom M n false)

instance noPrincipalFrom_persistent (M : AuthMode) (n : Nat) (ctx : GoInterface) :
    Persistent (noPrincipalFrom (GF := GF) M n ctx) := by
  unfold noPrincipalFrom; infer_instance

/-- **The context's token was refused, seen with the lower bound `n`** (persistent): until token
liveness (the Scope's G5), only that the context carries a token. -/
def tokRefusedFrom (_M : AuthMode) (_n : Nat) (ctx : GoInterface) : IProp GF :=
  iprop(⌜∃ t : GoString, ctxTokenOf ctx = some t⌝)

instance tokRefusedFrom_persistent (M : AuthMode) (n : Nat) (ctx : GoInterface) :
    Persistent (tokRefusedFrom (GF := GF) M n ctx) := by
  unfold tokRefusedFrom; infer_instance

end defs

section refusal
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`IsAdminPermitted` refused at states no older than `n`** (persistent; auth-guard-completeness
G1): the flag read at a state recorded at an index at least `n`, the user at another such state, and
the check refuses in them (`adminRefused`). -/
def adminRefusedFrom (γa : AuthNames) (n : Nat) (ai : Option AuthInfoM) : IProp GF :=
  iprop(∃ (i j : Nat) (sf su : AuthState), authStateAt γa i sf ∗ authStateAt γa j su ∗
    ⌜n ≤ i ∧ n ≤ j ∧ adminRefused sf su ai⌝)

instance adminRefusedFrom_persistent (γa : AuthNames) (n : Nat) (ai : Option AuthInfoM) :
    Persistent (adminRefusedFrom (GF := GF) γa n ai) := by
  unfold adminRefusedFrom; infer_instance

/-- **The error of an admin refusal** (persistent): `ErrUserEmpty`, or, for a non-`nil` auth info,
`ErrUserNotFound` or `ErrPermissionDenied`. -/
def adminErrOf (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    IProp GF :=
  iprop(authErrOf .userEmpty err ∨
    (⌜oinfo.isSome = true⌝ ∗ (authErrOf .userNotFound err ∨ authErrOf .permissionDenied err)))

instance adminErrOf_persistent (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : Persistent (adminErrOf (GF := GF) oinfo err) := by
  unfold adminErrOf; infer_instance

/-- **`IsAdminPermitted`'s verdict no older than `n`, both halves** (persistent), for the auth info
`oinfo` (`none`: a `nil` pointer): in `on γa`, a pass admits the principal (`adminOk`) at a state
recorded at an index at least `n`, and a refusal refuses it at such states (`adminRefusedFrom`) with
one of the check's errors (`adminErrOf`); in `off`, a pass; in `any`, nothing. -/
def adminVerdictFromO (M : AuthMode) (n : Nat) (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa => iprop((∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
        ⌜n ≤ i ∧ (err = GoInterface.nil → adminOk st (oinfo.map authInfoM))⌝) ∗
      (∀ _ : err ≠ GoInterface.nil, adminRefusedFrom γa n (oinfo.map authInfoM) ∗
        adminErrOf oinfo err))

instance adminVerdictFromO_persistent (M : AuthMode) (n : Nat)
    (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    Persistent (adminVerdictFromO (GF := GF) M n oinfo err) := by
  unfold adminVerdictFromO; cases M <;> infer_instance

end refusal

end auth

end EtcdGrove
end Perennial
