/-
**etcd's members never refuse** (D29, 2026-10-21; `notes/read-retry-plan.md`): the trust boundary.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.UnaryChain
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.net.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server listening at `addr` serves etcd's KV service over the server `s`, behind the unary
chain `ics`** (persistent; 2026-11-24, `notes/axiom-review/norefusal-link.md`): the server `γ` listening
at `addr` (`grpcAddrIs`, made by `grpc.start` and `bridge.New` only, one per address by
`grpcAddrIs_agree`) was built with Go's configuration `c` (`grpcSrvCfg`, one per server by
`grpcSrvCfg_agree`), whose unary chain is `ics` and whose unary registrations include the KV service's
on the quota wrapper `q` over the `*kvServer` `p` of `s` (`kvRegs q`, `quotaKVServerAt`). What the
started theorems (`client.etcd_kv_started_with`, ...) return, from `grpc.start'`'s `grpcServerAt`. -/
def etcdKVSrvAt (addr : GoString) (s : Loc) (ics : List GoFunc) : IProp GF :=
  iprop(∃ (γ : GName) (c : GrpcSrvCfg GF) (q p : Loc),
    ⌜(∀ x ∈ v3rpc.kvRegs q, x ∈ c.regs) ∧ c.ics = ics⌝ ∗
    grpcAddrIs addr γ ∗ grpcSrvCfg γ c ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s)

instance etcdKVSrvAt_persistent (addr : GoString) (s : Loc) (ics : List GoFunc) :
    Persistent (etcdKVSrvAt (GF := GF) addr s ics) := by
  unfold etcdKVSrvAt; infer_instance

/-- **The server listening at `addr` is etcd's over `s`** (persistent): `etcdKVSrvAt` at etcd's own
unary chain over `s` (`v3rpc.etcdUnaryIcs`, by identity): what `etcd_noRefusal` and
`etcd_noOtherRefusal` take, bundled. -/
def etcdKVSrv (addr : GoString) (s : Loc) : IProp GF :=
  iprop(∃ ics : List GoFunc, etcdKVSrvAt addr s ics ∗ v3rpc.etcdUnaryIcs s ics)

instance etcdKVSrv_persistent (addr : GoString) (s : Loc) :
    Persistent (etcdKVSrv (GF := GF) addr s) := by
  unfold etcdKVSrv; infer_instance

/-- `etcdKVSrv` from its two halves. -/
theorem etcdKVSrv_intro (addr : GoString) (s : Loc) (ics : List GoFunc) :
    etcdKVSrvAt (GF := GF) addr s ics ∗ v3rpc.etcdUnaryIcs s ics ⊢ etcdKVSrv addr s := by
  iintro ⟨#H1, #H2⟩
  unfold etcdKVSrv
  iexists ics
  iframe #

/-- **`etcdKVSrvAt` from `grpc.start'`'s fact** (`grpcServerAt`): the server `γ` listening at `addr`,
built with the unary chain `ics` and the unary registrations `regs`, which include the KV service's
on `q` over `p` of `s`. -/
theorem etcdKVSrvAt_of_serverAt (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (γ : GName) (q p s : Loc)
    (hregs : ∀ x ∈ v3rpc.kvRegs q, x ∈ regs) :
    grpcServerAt addr ics regs tys γ ∗
      v3rpc.quotaKVServerAt q
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ⊢
      etcdKVSrvAt addr s ics := by
  iintro ⟨#Hs, #Hq⟩
  iunfold grpcServerAt at Hs
  icases Hs with ⟨#Ha, ⟨%sics, %sregs, #Hc⟩, -⟩
  unfold etcdKVSrvAt
  iexists γ, ({ ics := ics, sics := sics, regs := regs, sregs := sregs } : GrpcSrvCfg GF), q, p
  iframe #
  ipureintro; exact ⟨hregs, rfl⟩

end defs

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An etcd member never answers a KV call with a refusal** (an axiom; D29; narrowed to the KV
service 2026-10-23; restated over the server listening at the address 2026-11-24: `notes/decisions.md`, "`etcd_noRefusal` over the server listening at the address").
The server `γ` listening at `addr` (`grpcAddrIs`), built with Go's configuration `c` (`grpcSrvCfg`)
whose registrations include the KV service on the quota wrapper `q` over the server `s` (`kvRegs q`
among `c.regs`) and whose unary chain is etcd's over `s` (`v3rpc.etcdUnaryIcs s c.ics`, by identity:
the closures `newLogUnaryInterceptor(s)` and `newUnaryInterceptor(s)` return and one of
grpc-prometheus's, in `v3rpc.Server`'s order and nothing else): if `s` runs with authentication off
(`E.authOn = false`: a fresh backend, `NewAuthStore`'s `isAuthStore … false`) and as a voter (the
server model boots a new cluster's member; a voter stays one unless a conf change re-adds it as a
learner, which `ccLogOk`, the conf-change policy of `isServerReq`'s raft log invariant, does not
exclude: the voter fact is assumed, see the end), no status `γ` sends in answer to a call of the KV
service (`kvMethod`) has a refusal's description (`noRefusalAt addr`).

**Why the server listening at `addr`** (2026-11-24, `notes/axiom-review/norefusal-link.md`). Until then
the axiom took etcd's server being built (`grpcSrvNew gs …`) and any listener at `addr`
(`netListenerAt lis addr`) and gave both back with the pure, global `noRefusalAt addr`: nothing tied
`addr` to `gs`, so a program could build `gs`, never serve it, and serve `addr` with another gRPC server
whose KV `Put` returns the learner refusal; the attempt contract (`grpcInvokerOk`) then said a `Put`
at `addr` is never refused, and Go refuses it (`examples/axiomcx/norefusal`, `Main`). Now the premise
is the server at `addr` itself: `grpcAddrIs addr γ` is made only by `grpc.start` (from that server's
`grpcSrvNew` and the listener, which it consumes) and `bridge.New` (an address relaying to the server
at another, whose answers it relays unchanged, as its spec's `noRefusalAt` carry says), one per
address (`grpcAddrIs_agree`), and `grpcSrvCfg γ c` is that server's configuration, one per server
(`grpcSrvCfg_agree`). Every instance of this statement is an instance of the old one at the moment
of the start (the old premises held then, `isServerReq` and `quotaKVServerAt` being persistent) or
the old one at the bridged address and the bridge's carry: the statement is weaker.

**Why etcd's chain, by identity** (2026-11-24, the same review). With only the registrations read,
a server registering etcd's KV service over `s` behind an interceptor of the program's that answers
every call with a refusal met the premises, and Go refuses (`examples/axiomcx/norefusal`,
`MainInterceptor`): an interceptor's contract (`srvInterceptorOk`) allows any non-handler error, the
learner refusal among them (etcd's own interceptor returns it at a learner). So the chain is named by
value: `v3rpc.isLogUnaryIc`/`isUnaryIc` (the constructors' closures over a variable holding `s`, read
off their translated code and returned by their proved specs) and `promUnaryIc` (grpc-prometheus's,
named by its trusted spec, restated for this). Weaker again: every server meeting the premises was
built by a `grpcSrvNew` with that chain, which the old axiom's premises allowed.

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
the old balancer's two strings occurs in grpc v1.84). Not every method of the server is
refusal-free, which is why the claim is about the KV service: the Auth service's `UserAdd` of an
empty name returns `auth.ErrUserEmpty` with authentication off (`authStore.UserAdd`), and the watch
stream's cancel reasons use the auth strings. Not proved: the server's specs describe its errors by
structure, not identity (`notes/read-retry-plan.md` R1), and `IsLearner`'s spec returns any boolean,
so the voter fact rests on this axiom too. -/
axiom etcd_noRefusal (addr : GoString) (γ : GName) (c : GrpcSrvCfg GF) (q p s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) :
  (∀ x ∈ v3rpc.kvRegs q, x ∈ c.regs) → E.authOn = false →
  isServerReq s E ρ ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
    grpcAddrIs addr γ ∗ grpcSrvCfg γ c ∗ v3rpc.etcdUnaryIcs s c.ics ⊢
  ⌜noRefusalAt addr⌝

/-- **An etcd member never answers a KV call with a non-auth refusal, in either auth mode** (an
axiom; F-S2 part 1, 2026-10-29, approved by the user; reviewed 2026-10-29 for what the member
answers, `notes/axiom-review/etcd-noOtherRefusal.md`, and refuted 2026-11-24 for which server answers
at `addr`: restated over the server listening at the address and its chain, as `etcd_noRefusal`,
whose old statement's two holes it shared, `notes/axiom-review/norefusal-link.md`). As `etcd_noRefusal`, without its premise
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
axiom etcd_noOtherRefusal (addr : GoString) (γ : GName) (c : GrpcSrvCfg GF) (q p s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) :
  (∀ x ∈ v3rpc.kvRegs q, x ∈ c.regs) →
  isServerReqM E.authOn s E ρ ∗
    v3rpc.quotaKVServerAt q
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
    grpcAddrIs addr γ ∗ grpcSrvCfg γ c ∗ v3rpc.etcdUnaryIcs s c.ics ⊢
  ⌜noOtherRefusalAt addr⌝

end axioms

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`etcd_noRefusal` at `etcdKVSrvAt` and etcd's chain**: the address whose server serves etcd's
KV service over a member with authentication off, behind etcd's unary chain, is refusal-free. -/
theorem etcd_noRefusal_at (addr : GoString) (s : Loc) (ics : List GoFunc) (E : apply.AEnv GF)
    (ρ : ReqNames) (hoff : E.authOn = false) :
    isServerReq s E ρ ∗ etcdKVSrvAt addr s ics ∗ v3rpc.etcdUnaryIcs s ics ⊢ ⌜noRefusalAt addr⌝ := by
  iintro ⟨#Hreq, #Hat, #Hics⟩
  iunfold etcdKVSrvAt at Hat
  icases Hat with ⟨%γ, %c, %q, %p, ⟨%hregs, %hics⟩, #Ha, #Hc, #Hq⟩
  subst hics
  iapply (etcd_noRefusal addr γ c q p s E ρ hregs hoff)
  iframe #

/-- **`etcd_noRefusal` at `etcdKVSrv`** (the bundle). -/
theorem etcd_noRefusal_srv (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (hoff : E.authOn = false) :
    isServerReq s E ρ ∗ etcdKVSrv addr s ⊢ ⌜noRefusalAt addr⌝ := by
  iintro ⟨#Hreq, #Hk⟩
  iunfold etcdKVSrv at Hk
  icases Hk with ⟨%ics, #Hat, #Hics⟩
  iapply (etcd_noRefusal_at addr s ics E ρ hoff)
  iframe #

end laws

end EtcdGrove
end Perennial
