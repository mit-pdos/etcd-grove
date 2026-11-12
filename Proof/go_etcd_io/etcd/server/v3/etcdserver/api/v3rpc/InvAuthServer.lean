/-
**The gRPC Auth service** (the auth plan's A3, the API layer, 2026-10-24; `notes/auth-plan.md`):
`auth.go`'s `AuthServer`, whose seventeen methods call the server's method of the same name
through the `Authenticator` interface and pass its error through `togRPCError`. Lean-first (no
Rocq counterpart); the server side is `etcdserver/AuthEntry.lean`.

**The object** (`authServerIs p s`, persistent): the `*AuthServer` `p` whose `authenticator` is the
server `s` (`NewAuthServer`'s `&AuthServer{authenticator: s}`).

**The inner call as a contract** (`authInnerOk s m ctx r P Q`): the server's method `m` on `(ctx,
r)` over the caller's `P`, answering as the entry points do (`authEntryOut Q`, with an error the
apply package's facts describe); the wrapper's outcome (`authWrapOut Q resp err`): the server's
response with `Q resp nil`, or `nil` and a non-nil error (`togRPCError`'s) with `Q null` of the
server's error. As the maintenance wrappers' (`InvAuthAdmin.lean`), the gRPC layer's proof is
closed over the server's contract; the entry points' own specs are the server's
(`Spec/.../etcdserver/EtcdServer__AuthEnable.lean`, ...).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthAdmin
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthEntry

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*AuthServer` `p`** (read-only): its `authenticator` is the server `s`. -/
def authServerIs (p s : Loc) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer go!"authenticator" p ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface))

instance authServerIs_persistent (p s : Loc) : Persistent (authServerIs (GF := GF) p s) := by
  unfold authServerIs; infer_instance

/-- **The server's method `m` on `(ctx, r)`, as a contract** (persistent): over the caller's `P`,
answering as the entry points do (`authEntryOut Q`). -/
def authInnerOk (s : Loc) (m : GoString) (ctx : GoInterface) (r : Loc) (P : IProp GF)
    (Q : Loc → GoInterface → IProp GF) : IProp GF :=
  iprop({{ P }} (App (App (Val (srvM s m)) (Val #ctx)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); applyErrIs err ∗ authEntryOut Q resp err }})

instance authInnerOk_persistent (s : Loc) (m : GoString) (ctx : GoInterface) (r : Loc)
    (P : IProp GF) (Q : Loc → GoInterface → IProp GF) : Persistent (authInnerOk s m ctx r P Q) := by
  unfold authInnerOk; infer_instance

/-- **A wrapper's outcome**: the server's response with `Q resp nil`, or `nil` and a non-nil error
(one grpc's server handles, `srvErrOk`: a `status` error, k8s etcd3 7c, HS-6, or a `%w` chain to a
context error, errorf-wrap) with `Q null` of the
server's (non-nil) error. -/
def authWrapOut (Q : Loc → GoInterface → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ Q resp GoInterface.nil) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗
      ∃ e0 : GoInterface, ⌜e0 ≠ GoInterface.nil⌝ ∗ Q null e0))

open Iris.ProofMode in
/-- A wrapper's error is one grpc's `status.FromError` accepts (`nil` on success). -/
theorem authWrapOut_srvErrOk (Q : Loc → GoInterface → IProp GF) (resp : Loc) (err : GoInterface) :
    authWrapOut Q resp err ⊢ go_etcd_io.etcd.cache.v3.srvErrOk err ∗ authWrapOut Q resp err := by
  iintro Hout
  iunfold authWrapOut at Hout
  icases Hout with (⟨%Hn, HQ⟩ | ⟨%Hn, #Hse, HQ⟩)
  · subst Hn
    isplitr
    · iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil
    iunfold authWrapOut; ileft; iframe HQ; ipureintro; rfl
  · iframe Hse
    iunfold authWrapOut; iright; iframe HQ Hse; ipureintro; exact Hn

end defs

end v3rpc
end EtcdGrove
end Perennial
