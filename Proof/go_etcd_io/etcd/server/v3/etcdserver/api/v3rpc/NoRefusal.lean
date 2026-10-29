/-
**etcd's members never refuse** (D29, 2026-10-21; `notes/read-retry-plan.md`): the trust boundary.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.net.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An etcd member never answers a KV call with a refusal** (an axiom; D29; narrowed to the KV
service 2026-10-23). The gRPC server `gs`, built by `v3rpc.Server(s, ...)` with the quota wrapper
`q` over the KV service of the server `s` (`kvRegs q` among its registrations), about to be served
on the listener `lis` at `addr`: if `s` runs with authentication off (`E.authOn = false`: a fresh
backend, `NewAuthStore`'s `isAuthStore … false`) and as a voter (the server model boots a new
cluster's member; a voter stays one unless a conf change re-adds it as a learner, which `ccLogOk`,
the conf-change policy of `isServerReq`'s raft log invariant, does not exclude: the voter fact is
assumed, see the end), no status `gs` sends in answer to a
call of the KV service (`kvMethod`) has a refusal's description (`noRefusalAt addr`).

True of etcd at the pin, by its code: a KV call's error reaches the client through the unary
interceptor and `togRPCError`. The four etcd refusals (`refusalDescs`) are `togRPCError`'s map
entries for `auth.ErrUserEmpty`, `ErrInvalidAuthToken` and `ErrAuthOldRevision`
(`v3rpc/util.go:78-91`; the auth errors' own messages start `"auth: "`) and the unary interceptor's
learner branch (`interceptor.go:54`). On a KV call those auth errors come only from
`AuthInfoFromCtx`, `isOpPermitted`, `IsAdminPermitted` and `doSerialize`'s revision check, each of
which returns them only with authentication enabled (`if !as.IsAuthEnabled() { return nil }`), and
the learner branch runs only at a learner. Any other error reaches the client through
`togRPCError`'s other entries or its default case, whose message is `err.Error()`, an error of the
server's own, none of the six strings; grpc's server-side errors carry grpc's messages (neither of
the old balancer's two strings occurs in grpc v1.84). Not every method of `gs` is refusal-free,
which is why the claim is about the KV service: the Auth service's `UserAdd` of an empty name
returns `auth.ErrUserEmpty` with authentication off (`authStore.UserAdd`), and the watch stream's
cancel reasons use the auth strings. Not proved: the server's specs describe its errors by
structure, not identity (`notes/read-retry-plan.md` R1), and `IsLearner`'s spec returns any
boolean, so the voter fact rests on this axiom too. -/
axiom etcd_noRefusal (addr : GoString) (gs q p s : Loc) (lis : GoInterface) (E : apply.AEnv GF)
    (ρ : ReqNames) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × val × GoInterface)) :
  (∀ x ∈ v3rpc.kvRegs q, x ∈ regs) → E.authOn = false →
  isServerReq s E ρ ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
    grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
  grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ∗ ⌜noRefusalAt addr⌝

/-- **An etcd member never answers a KV call with a non-auth refusal, in either auth mode** (an
axiom; F-S2 part 1, 2026-10-29, approved by the user; reviewed: survives under the voter condition,
`notes/axiom-review/etcd-noOtherRefusal.md`). As `etcd_noRefusal`, without its premise
`E.authOn = false`, over the server's view in its mode (`isServerReqM E.authOn`), and with the
conclusion narrowed to the descriptions that do not depend on authentication
(`noOtherRefusalAt addr`: the learner's refusal and the old balancer's two).

True of etcd at the pin, by its code: the learner refusal (`rpctypes.ErrGRPCNotSupportedForLearner`)
is returned only by the interceptors' learner branch (`interceptor.go:54` unary, `:225` stream),
under `s.IsMemberExist(s.MemberID()) && s.IsLearner() && !isRPCSupportedForLearner(req)`; nothing on
the auth path (`AuthInfoFromCtx`, the apply's permission checks, `auth/store.go`) returns it. The
balancer strings occur only in the client (`client/v3/retry.go:93`), in neither the server nor grpc
v1.84. Authentication changes neither: a conf change is applied the same in both modes.

**The voter assumption.** The learner branch is excluded only if the member is a voter for its
whole life. The server model boots a new cluster's member as a voter, and etcd has no demotion of a
voter (only `PromoteMember`, learner to voter); but a conf change re-adding the member as a learner
is not excluded by `ccLogOk` (the conf-change policy of the raft log invariant: a conf change's id is
`0` and `applyConfChange` takes it), and `IsLearner`'s spec returns any boolean. So the voter fact is
part of what this axiom assumes, as for `etcd_noRefusal`. -/
axiom etcd_noOtherRefusal (addr : GoString) (gs q p s : Loc) (lis : GoInterface)
    (E : apply.AEnv GF) (ρ : ReqNames) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × val × GoInterface)) :
  (∀ x ∈ v3rpc.kvRegs q, x ∈ regs) →
  isServerReqM E.authOn s E ρ ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
    grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
  grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ∗ ⌜noOtherRefusalAt addr⌝

end axioms

end EtcdGrove
end Perennial
