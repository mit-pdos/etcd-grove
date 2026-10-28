/-
**etcd's members never refuse** (D29, 2026-10-21; `notes/read-retry-plan.md`): the trust boundary.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
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
cluster's member, with the membership changes it takes keeping it a voter, `srvCCPolicy` in
`isServerReq`'s raft log invariant: an `AddNode` of a voter), no status `gs` sends in answer to a
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

end axioms

end EtcdGrove
end Perennial
