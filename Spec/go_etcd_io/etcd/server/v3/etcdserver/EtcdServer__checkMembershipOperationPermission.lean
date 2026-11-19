/-
`s.checkMembershipOperationPermission(ctx)` (`server.go`): the admin guard of the membership
operations (`AddMember`, `RemoveMember`, `UpdateMember`, `promoteMember`). Lean-first (no Rocq
counterpart); the auth plan's A2 (2026-10-23), vocabulary `AuthGuard.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthWhy
public import Proof.context.LibKeys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.checkMembershipOperationPermission(ctx)` with why it refused (auth-guard-completeness G2,
2026-11-14; `notes/auth-guard-scope.md`, §2.3), for a caller holding a lower bound `n` of the auth
store's published index (`auth.authPubLbM`): the outcome with the binding (`adminOutB`), and on an error the admin class's reason
(`adminOutC`'s `adminWhy`). With auth on: the request side's (as `requireAuthInfo.specC`, its
flag race here one with `AuthEnable`: `AuthInfoFromCtx` reads `false`, then `IsAdminPermitted` `true`,
`nonissues/etcd-admin-check-authenable-race.md`), or a
principal bound to the request that `IsAdminPermitted` refused with the flag `true` at a state no
older than `n`: `ErrUserEmpty` for an unnamed one, `ErrUserNotFound` for a user absent at such a
state, `ErrPermissionDenied` for one present there without the root role. With the history frozen
from `n` on, auth enabled, a token in the context and every principal bound to it root, only
`ErrInvalidAuthToken` remains (`admin_served_of_frozen`). With auth off, it says nothing of an error
from `AuthInfoFromCtx`: the off store's request side (`isReqAuth`, of `NewAuthStore`'s axiom) does
not say there is none (a follow-up of D22: discharging `NewAuthStore`'s axiom by proof would give "no
error with auth off" without new trust; decided by etcd-grove-81, 2026-11-14). `IsAdminPermitted(nil)`'s clause (`srvAdminNilOk`) is not a premise:
`srvAuthAt` gives it (`srvAdminNilOk_of_srvAuthAt`). -/
abbrev EtcdServer.checkMembershipOperationPermission.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString)
    (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗
      E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"checkMembershipOperationPermission")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ adminOutC s E.authMode n tok err }}

end spec

end EtcdGrove
end Perennial
