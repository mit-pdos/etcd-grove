/-
**grpc's dial: the client side's producer** (item 5, client construction, 2026-10-17; branch
`construct`). Lean-first (no Rocq counterpart). Until now nothing produced the client's connection
`grpcConn conn addr ics dopts` (`InvGrpc.lean`): `client_*_end_to_end` took it as a premise. Here,
grpc's `NewClient` produces it, from what the dial options set (the axioms of the option
constructors, `Spec/google_golang_org/grpc/With*.lean`, and of `NewClient`,
`Spec/google_golang_org/grpc/NewClient.lean`).

**Dial options** (`GrpcDialOpt`, `grpcDialOptIs o d`): a `grpc.DialOption` is opaque (grpc's
`funcDialOption`, a closure over grpc's `dialOptions`); `grpcDialOptIs o d` says that the option `o`
does `d` to the dial's options. The descriptors are those `clientv3.New` passes (its `dialSetupOpts`
and `dialWithBalancer`); an option only an axiom of its constructor introduces, so every option a
proof holds a descriptor of is one of these:
* `.unaryInterceptor ic` (`WithUnaryInterceptor(ic)`: sets `dopts.unaryInt`; the last one wins);
* `.streamInterceptor ic` (`WithStreamInterceptor(ic)`: sets `dopts.streamInt`; the last wins);
* `.transportCreds` (`WithTransportCredentials(c)`: sets `dopts.copts.TransportCredentials`);
* `.resolvers rbs` (`WithResolvers(rbs...)`: appends to `dopts.resolvers`, the builders `NewClient`
  looks the target's scheme up in before grpc's global registry);
* `.keepalive` (`WithKeepaliveParams(kp)`: sets `dopts.copts.KeepaliveParams`, since 2026-10-21,
  `notes/decisions.md` D28): it sets no interceptor and no resolver; at run time the transport
  pings and closes the connection when a ping goes unanswered, which fails the calls on it, as
  `ClientConn.Invoke`'s and `NewStream`'s axioms already allow.
An option a descriptor does not describe (`WithChainUnaryInterceptor`, `WithDefaultCallOptions`,
per-RPC credentials, ...) has no descriptor: a dial that holds one is not covered
(`clientv3.New`'s premises exclude `Config.DialOptions`,
`issues/etcd-client-dialoptions-unary-interceptor.md`).

**The unary chain** (`unaryIcsOf ds`): grpc's `chainUnaryClientInterceptors` runs `dopts.unaryInt`
(the last `WithUnaryInterceptor`'s) first, then `dopts.chainUnaryInts`, which no descriptor sets:
the chain is the last `.unaryInterceptor`'s, or empty. No descriptor sets default call options
(`WithDefaultCallOptions`): they are `[]`.

**The stream interceptor** (`etcdStreamInterceptor si`, an axiomatized property): grpc's
`ClientConn.NewStream` axiom (`Spec/google_golang_org/grpc/ClientConn__NewStream.lean`) assumes the
connection's stream interceptor is etcd's (`streamClientInterceptor`, `retry_interceptor.go`), so
`NewClient` gives `grpcConn` only for a dial whose stream interceptors are etcd's; the property is
introduced only by the client's `streamClientInterceptor` axiom
(`Spec/go_etcd_io/etcd/client/v3/Client__streamClientInterceptor.lean`).

**The resolver** (`grpcResolverAt rb scheme addrs`, exclusive, axiomatized): the resolver builder
`rb` (a `resolver.Builder`), for the scheme `scheme`, resolves to the addresses `addrs`, for good
(a list since 2026-10-21, `notes/decisions.md` D27; one address until then):
the resolver's state is grpc's once it is dialed with (`NewClient` takes it). etcd's
`EtcdManualResolver` gives it for plain endpoints (`client/v3/InvNew.lean`,
`etcdResolver_grpc`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax]

/-- **What a dial option does** (see the file header). -/
inductive GrpcDialOpt where
  | unaryInterceptor (ic : GoFunc)
  | streamInterceptor (ic : GoFunc)
  | transportCreds
  | resolvers (rbs : List GoInterface)
  | keepalive

/-- The unary interceptor a descriptor sets, if it sets one. -/
def GrpcDialOpt.unaryOf : GrpcDialOpt → Option GoFunc
  | .unaryInterceptor ic => some ic
  | _ => none

/-- The stream interceptor a descriptor sets, if it sets one. -/
def GrpcDialOpt.streamOf : GrpcDialOpt → Option GoFunc
  | .streamInterceptor ic => some ic
  | _ => none

/-- **The unary interceptor chain of a dial with the options `ds`** (see the file header): the
last `WithUnaryInterceptor`'s, or none. -/
def unaryIcsOf (ds : List GrpcDialOpt) : List GoFunc :=
  match (ds.filterMap GrpcDialOpt.unaryOf).getLast? with
  | some ic => [ic]
  | none => []

/-- Keepalive sets no unary interceptor. -/
theorem unaryIcsOf_keepalive (ds : List GrpcDialOpt) :
    unaryIcsOf (.keepalive :: ds) = unaryIcsOf ds := by
  unfold unaryIcsOf
  simp [List.filterMap_cons, GrpcDialOpt.unaryOf]

end defs

/-- **The dial option `o` does `d`** (an axiomatized property: introduced only by the axioms of
grpc's option constructors; see the file header). -/
axiom grpcDialOptIs [FfiSyntax] (o : GoInterface) (d : GrpcDialOpt) : Prop

/-- **`si` is etcd's client stream interceptor** (an axiomatized property: introduced only by the
client's `streamClientInterceptor` axiom; what grpc's `ClientConn.NewStream` axiom assumes of a
connection's stream interceptor). -/
axiom etcdStreamInterceptor [FfiSyntax] (si : GoFunc) : Prop

/-- **The resolver builder `rb` resolves the scheme `scheme` to the addresses `addrs`** (exclusive; an
axiomatized predicate; see the file header). -/
axiom grpcResolverAt {GF : BundledGFunctors} [FfiSyntax] (rb : GoInterface) (scheme : GoString)
  (addrs : List GoString) : IProp GF

section defs2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The slice `sl` of dial options, read-only, doing `ds`** (persistent). -/
def dialOptsAt (sl : GoSlice) (ds : List GrpcDialOpt) : IProp GF :=
  iprop(∃ os : List GoInterface, sl ↦*□ os ∗ ⌜List.Forall₂ grpcDialOptIs os ds⌝)

instance dialOptsAt_persistent (sl : GoSlice) (ds : List GrpcDialOpt) :
    Persistent (dialOptsAt (GF := GF) sl ds) := by
  unfold dialOptsAt; infer_instance

/-- **A dial `NewClient` connects with** (pure): its stream interceptors are etcd's, and its one
resolver is `rb` (every `WithResolvers` of the dial gives `rb` alone, and one does). -/
def dialOk (ds : List GrpcDialOpt) (rb : GoInterface) : Prop :=
  (∀ si, GrpcDialOpt.streamInterceptor si ∈ ds → etcdStreamInterceptor si) ∧
    (∀ rbs, GrpcDialOpt.resolvers rbs ∈ ds → rbs = [rb]) ∧ GrpcDialOpt.resolvers [rb] ∈ ds


/-- Keepalive sets no stream interceptor and no resolver: a dial with it is `NewClient`'s if the
dial without it is. -/
theorem dialOk_keepalive (ds : List GrpcDialOpt) (rb : GoInterface) :
    dialOk ds rb → dialOk (.keepalive :: ds) rb := by
  intro ⟨h1, h2, h3⟩
  refine ⟨fun si h => h1 si ?_, fun rbs h => h2 rbs ?_, List.mem_cons_of_mem _ h3⟩
  · simpa using h
  · simpa using h

end defs2

end EtcdGrove
end Perennial
