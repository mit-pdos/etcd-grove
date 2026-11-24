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
  `ClientConn.Invoke`'s and `NewStream`'s axioms already allow;
* `.perRPCCreds c` (`WithPerRPCCredentials(c)`: appends to `dopts.copts.PerRPCCredentials`, since
  2026-10-25, the auth plan's E2d: a client with a user name): it sets no interceptor and no
  resolver; at run time each attempt's outgoing metadata gains what the credentials'
  `GetRequestMetadata` returns (etcd's: its token, if any), and an error of theirs fails the
  attempt, which the attempt contract (`grpcInvokerOk`) already allows; what the credentials
  return to the attempts is `connCredsOk` (`NewClient`'s post, since the auth plan's C1).
An option a descriptor does not describe (`WithChainUnaryInterceptor`, `WithDefaultCallOptions`,
...) has no descriptor: a dial that holds one is not covered
(`clientv3.New`'s premises exclude `Config.DialOptions`,
`nonissues/etcd-client-dialoptions-unary-interceptor.md`).

**The unary chain** (`unaryIcsOf ds`): grpc's `chainUnaryClientInterceptors` runs `dopts.unaryInt`
(the last `WithUnaryInterceptor`'s) first, then `dopts.chainUnaryInts`, which no descriptor sets:
the chain is the last `.unaryInterceptor`'s, or empty. No descriptor sets default call options
(`WithDefaultCallOptions`): they are `[]`.

**The stream interceptor** (`streamIcMdIs si F`, an axiomatized property; grpc-trusted-T, T7,
2026-11-24): what grpc's `ClientConn.NewStream` axiom assumes of a connection's stream interceptor,
that it passes the caller's call on with its outgoing metadata `F`-related to the caller's; introduced
only by an interceptor's own axiom (etcd's `streamClientInterceptor`). `NewClient` gives the
connection's options (`grpcConnOpts conn (connOptsOf ds)`), from which `NewStream` states the attempt's
metadata (`streamMdOk`: none, the caller's; one, its `F`) and errors (grpc's own shape with none).
Until T7 `NewClient` required the dial's stream interceptor to be etcd's (`etcdStreamInterceptor`, now
etcd's name for `streamIcMdIs` at its relation).

**The passthrough resolver** (`dialPassthrough`, T7): a dial to `passthrough:///a` with no resolver
option reaches the one address `a`.

**The resolver** (`grpcResolverAt rb scheme addrs`, exclusive, axiomatized): the resolver builder
`rb` (a `resolver.Builder`), for the scheme `scheme`, resolves to the addresses `addrs`, for good
(a list since 2026-10-21, `notes/decisions.md` D27; one address until then):
the resolver's state is grpc's once it is dialed with (`NewClient` takes it), and its service
config sets no retry policy (k8s 7e-1, 2026-11-10, decided by etcd-grove-81: a `retryPolicy` that
exhausts its attempts makes grpc-go v1.84 return a `*fmt.wrapError`, `stream.go:867`, which
`grpcInvokerOk`/`cliStreamErr` exclude through `clientErr`; no dial option of `GrpcDialOpt` sets a
default service config). etcd's `EtcdManualResolver` gives it for plain endpoints
(`client/v3/InvNew.lean`, `etcdResolver_grpc`: `{"loadBalancingPolicy":"round_robin"}` only).
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
variable [GooseExts]

/-- **What a dial option does** (see the file header). -/
inductive GrpcDialOpt where
  | unaryInterceptor (ic : GoFunc)
  | streamInterceptor (ic : GoFunc)
  | transportCreds
  | resolvers (rbs : List GoInterface)
  | keepalive
  | perRPCCreds (pc : GoInterface)

/-- The per-RPC credentials a descriptor adds, if it adds some. -/
def GrpcDialOpt.credsOf : GrpcDialOpt → Option GoInterface
  | .perRPCCreds pc => some pc
  | _ => none

/-- **The per-RPC credentials of a dial with the options `ds`**, in order (grpc appends each
`WithPerRPCCredentials`'s to `dopts.copts.PerRPCCredentials`). -/
def credsOfDial (ds : List GrpcDialOpt) : List GoInterface := ds.filterMap GrpcDialOpt.credsOf

@[simp] theorem credsOfDial_nil : credsOfDial [] = [] := rfl

@[simp] theorem credsOfDial_cons (d : GrpcDialOpt) (ds : List GrpcDialOpt) :
    credsOfDial (d :: ds) = (d.credsOf.toList ++ credsOfDial ds) := by
  unfold credsOfDial; cases h : d.credsOf <;> simp [List.filterMap_cons, h]

theorem credsOfDial_append (ds ds' : List GrpcDialOpt) :
    credsOfDial (ds ++ ds') = credsOfDial ds ++ credsOfDial ds' := by
  unfold credsOfDial; exact List.filterMap_append

/-- The unary interceptor a descriptor sets, if it sets one. -/
def GrpcDialOpt.unaryOf : GrpcDialOpt → Option GoFunc
  | .unaryInterceptor ic => some ic
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

/-- Per-RPC credentials set no unary interceptor. -/
theorem unaryIcsOf_perRPCCreds (ds : List GrpcDialOpt) (pc : GoInterface) :
    unaryIcsOf (ds ++ [.perRPCCreds pc]) = unaryIcsOf ds := by
  unfold unaryIcsOf
  simp [List.filterMap_append, GrpcDialOpt.unaryOf]

end defs

/-- **The stream interceptor `si` gives grpc's streamer the caller's call, its outgoing metadata
`F`-related to the caller's** (an axiomatized property, grpc-trusted-T, T7, 2026-11-24; introduced
only by an interceptor's own axiom: etcd's `streamClientInterceptor`, whose `withVersion` sets
`client-api-version`; until T7 the etcd-specific `etcdStreamInterceptor`, now etcd's name for this at
its relation, `client/v3/InvKVConn.lean`): called by `ClientConn.NewStream` with the caller's context
`ctx` (outgoing metadata `om`), a client-streaming descriptor, a method, options and grpc's streamer,
it calls the streamer at most once (or fails), synchronously, with the descriptor, method and options and a context whose outgoing metadata
`om'` has `F om om'` (and the caller's other values and cancellation), and returns what the streamer
returned, the stream possibly wrapped so that its operations are the streamer's stream's, their
errors those `cliStreamErr` admits. What grpc's `ClientConn.NewStream` axiom assumes of a
connection's stream interceptor. -/
axiom streamIcMdIs [GooseExts] (si : GoFunc) (F : GrpcMd → GrpcMd → Prop) : Prop

/-- **The resolver builder `rb` resolves the scheme `scheme` to the addresses `addrs`** (exclusive; an
axiomatized predicate; see the file header). -/
axiom grpcResolverAt {GF : BundledGFunctors} [GooseExts] (rb : GoInterface) (scheme : GoString)
  (addrs : List GoString) : IProp GF

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The fields of grpc's `dialOptions` the descriptors are about (`GrpcDialOpt`) other than the one
an option sets, unchanged. -/
def dialOptsKeep (d : GrpcDialOpt) (o o' : google_golang_org.grpc.dialOptions) : Prop :=
  (match d with | .unaryInterceptor _ => True | _ => o'.unaryInt' = o.unaryInt') ∧
  (match d with | .streamInterceptor _ => True | _ => o'.streamInt' = o.streamInt') ∧
  (match d with | .resolvers _ => True | _ => o'.resolvers' = o.resolvers') ∧
  (match d with
    | .perRPCCreds _ => True
    | _ => o'.copts'.PerRPCCredentials' = o.copts'.PerRPCCredentials')

/-- What an interceptor option sets (`unaryInt`, `streamInt`); nothing for the other descriptors. -/
def dialOptSets (d : GrpcDialOpt) (o' : google_golang_org.grpc.dialOptions) : Prop :=
  match d with
  | .unaryInterceptor ic => o'.unaryInt' = ic
  | .streamInterceptor ic => o'.streamInt' = ic
  | _ => True

/-- **What the closure `f` of a dial option `d` does to `*dialOptions`** (persistent; phase 7 S1,
`notes/phase7-plan.md`: grpc is the model's, `models/grpc`): applied to `p ↦ dopt`, it returns with
`p ↦ dopt'`, where `dopt'` sets what `d` sets (`.unaryInterceptor ic`: `unaryInt` is `ic`; likewise
`.streamInterceptor`; `.resolvers rbs`: the resolvers, whose elements `us` and capacity it is given,
are `us ++ rbs`; `.perRPCCreds pc`: the per-RPC credentials, likewise, `cs ++ [pc]`;
`.transportCreds`, `.keepalive`: fields no descriptor is about) and keeps the others
(`dialOptsKeep`). -/
def dialOptFnOk (f : GoFunc) : GrpcDialOpt → IProp GF
  | .resolvers rbs => iprop(□ ∀ (p : Loc) (dopt : google_golang_org.grpc.dialOptions)
      (us : List GoInterface) (Φ : val → IProp GF),
      p ↦ dopt -∗ dopt.resolvers' ↦* us -∗ ownSliceCap GoInterface dopt.resolvers' (DFrac.own 1) -∗
      ▷ (∀ dopt' : google_golang_org.grpc.dialOptions, p ↦ dopt' -∗
        dopt'.resolvers' ↦* (us ++ rbs) -∗ ownSliceCap GoInterface dopt'.resolvers' (DFrac.own 1) -∗
        ⌜dialOptsKeep (.resolvers rbs) dopt dopt'⌝ -∗ Φ #()) -∗
      WP (App (Val #f) (Val #p)) {{ Φ }})
  | .perRPCCreds pc => iprop(□ ∀ (p : Loc) (dopt : google_golang_org.grpc.dialOptions)
      (cs : List GoInterface) (Φ : val → IProp GF),
      p ↦ dopt -∗ dopt.copts'.PerRPCCredentials' ↦* cs -∗
      ownSliceCap GoInterface dopt.copts'.PerRPCCredentials' (DFrac.own 1) -∗
      ▷ (∀ dopt' : google_golang_org.grpc.dialOptions, p ↦ dopt' -∗
        dopt'.copts'.PerRPCCredentials' ↦* (cs ++ [pc]) -∗
        ownSliceCap GoInterface dopt'.copts'.PerRPCCredentials' (DFrac.own 1) -∗
        ⌜dialOptsKeep (.perRPCCreds pc) dopt dopt'⌝ -∗ Φ #()) -∗
      WP (App (Val #f) (Val #p)) {{ Φ }})
  | d => iprop(□ ∀ (p : Loc) (dopt : google_golang_org.grpc.dialOptions) (Φ : val → IProp GF),
      p ↦ dopt -∗ ▷ (∀ dopt' : google_golang_org.grpc.dialOptions, p ↦ dopt' -∗
        ⌜dialOptSets d dopt' ∧ dialOptsKeep d dopt dopt'⌝ -∗ Φ #()) -∗
      WP (App (Val #f) (Val #p)) {{ Φ }})

instance dialOptFnOk_persistent (f : GoFunc) (d : GrpcDialOpt) :
    Persistent (dialOptFnOk (GF := GF) f d) := by
  cases d <;> unfold dialOptFnOk <;> infer_instance

/-- **The dial option `o` does `d`** (persistent; a definition since phase 7 S1, 2026-11-22: grpc's
`*funcDialOption`, read-only, whose closure does `d`, `dialOptFnOk`; introduced by the option
constructors' specs). -/
def grpcDialOptIs (o : GoInterface) (d : GrpcDialOpt) : IProp GF :=
  iprop(∃ (l : Loc) (f : GoFunc),
    ⌜o = interface.mkOk (go.GoType.PointerType google_golang_org.grpc.funcDialOption.ty) #l⌝ ∗
    l ↦□ google_golang_org.grpc.funcDialOption.mk f ∗ dialOptFnOk f d)

instance grpcDialOptIs_persistent (o : GoInterface) (d : GrpcDialOpt) :
    Persistent (grpcDialOptIs (GF := GF) o d) := by
  unfold grpcDialOptIs; infer_instance

/-- **The slice `sl` of dial options, read-only, doing `ds`** (persistent). -/
def dialOptsAt (sl : GoSlice) (ds : List GrpcDialOpt) : IProp GF :=
  iprop(∃ os : List GoInterface, sl ↦*□ os ∗ [∗list] o;d ∈ os;ds, grpcDialOptIs o d)

instance dialOptsAt_persistent (sl : GoSlice) (ds : List GrpcDialOpt) :
    Persistent (dialOptsAt (GF := GF) sl ds) := by
  unfold dialOptsAt; infer_instance

/-- **A dial whose one resolver is `rb`** (pure): every `WithResolvers` of the dial gives `rb` alone,
and one does. (grpc-trusted-T, T7, 2026-11-24) Until then it also required the dial's stream
interceptors to be etcd's, and one (G2: `NewStream`'s post stated the metadata etcd's `withVersion`
adds); `NewStream` now states the attempt's metadata from the connection's options
(`grpcConnOpts`, `streamMdOk`), so `NewClient` dials with any interceptors. -/
def dialOk (ds : List GrpcDialOpt) (rb : GoInterface) : Prop :=
  (∀ rbs, GrpcDialOpt.resolvers rbs ∈ ds → rbs = [rb]) ∧ GrpcDialOpt.resolvers [rb] ∈ ds

/-- **A byte grpc's `passthrough` target keeps as it is** (pure): an ASCII letter or digit, or one of
`.`, `-`, `_`, `:`, `[`, `]`. `url.Parse` leaves a path of these bytes unchanged (no `%` escape, no
`?` query, no `#` fragment, no control byte, no `/`), so the passthrough resolver's
`Target.Endpoint()` (the path less its leading `/`) is the address itself. -/
def passthroughByteOk (b : w8) : Prop :=
  (48 ≤ b.toNat ∧ b.toNat ≤ 58) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 91) ∨ b.toNat = 93 ∨
    (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨ b.toNat = 45 ∨ b.toNat = 46 ∨ b.toNat = 95

/-- **A dial to the address `a` through grpc's `passthrough` resolver** (pure; grpc-trusted-T, T7,
2026-11-24): the target is `passthrough:///a`, `a` a non-empty address of `passthroughByteOk` bytes,
and the dial sets no resolver (`WithResolvers` would be looked up first): grpc resolves the target to
the one address `a` (`addrs = [a]`) with no service config, so no retry policy. True of grpc-go v1.84
and the model (`models/grpc`, `clientconn.go` `parseTargetAndFindResolver`: the target parses, its
scheme `passthrough` is the global registry's, which `internal/resolver/passthrough` registers at
init and no verified program re-registers, `resolver.Register` having no spec here;
`passthrough.go`'s resolver sends `[{Addr: target.Endpoint()}]` once and nothing else). -/
def dialPassthrough (ds : List GrpcDialOpt) (target : GoString) (addrs : List GoString) : Prop :=
  (∀ rbs, GrpcDialOpt.resolvers rbs ∉ ds) ∧
    ∃ a : GoString, a ≠ [] ∧ (∀ b ∈ a, passthroughByteOk b) ∧
      target = go!"passthrough:///" ++ a ∧ addrs = [a]

/-- **The connection's options a call's behavior depends on** (grpc-trusted-T, T7, 2026-11-24):
its unary interceptor chain, its stream interceptor (the last `WithStreamInterceptor`'s, or none),
its per-RPC credentials. -/
structure GrpcConnOpts where
  unaryIcs : List GoFunc
  streamIc : Option GoFunc
  creds : List GoInterface

/-- The stream interceptor a descriptor sets, if it sets one. -/
def GrpcDialOpt.streamOf : GrpcDialOpt → Option GoFunc
  | .streamInterceptor ic => some ic
  | _ => none

/-- **The stream interceptor of a dial with the options `ds`**: the last `WithStreamInterceptor`'s
(grpc's `dopts.streamInt`; no descriptor sets a chained one), or none. -/
def streamIcOf (ds : List GrpcDialOpt) : Option GoFunc :=
  (ds.filterMap GrpcDialOpt.streamOf).getLast?

/-- **The options of a connection dialed with `ds`**. -/
def connOptsOf (ds : List GrpcDialOpt) : GrpcConnOpts :=
  ⟨unaryIcsOf ds, streamIcOf ds, credsOfDial ds⟩

/-- **How a stream's attempt metadata follows from its caller's on a connection with the options
`d`** (pure; grpc-trusted-T, T7): with no stream interceptor, `F` is equality (grpc sends the
caller's outgoing metadata); with one, `F` is what it does (`streamIcMdIs`). -/
def streamMdOk (d : GrpcConnOpts) (F : GrpcMd → GrpcMd → Prop) : Prop :=
  (d.streamIc = none ∧ ∀ om om', F om om' ↔ om' = om) ∨
    ∃ si, d.streamIc = some si ∧ streamIcMdIs si F


/-- Keepalive sets no resolver: a dial with it is `NewClient`'s if the dial without it is. -/
theorem dialOk_keepalive (ds : List GrpcDialOpt) (rb : GoInterface) :
    dialOk ds rb → dialOk (.keepalive :: ds) rb := by
  intro ⟨h2, h3⟩
  refine ⟨fun rbs h => h2 rbs ?_, List.mem_cons_of_mem _ h3⟩
  simpa using h

/-- Per-RPC credentials set no resolver: a dial with them is `NewClient`'s if the dial without them
is. -/
theorem dialOk_perRPCCreds (ds : List GrpcDialOpt) (rb : GoInterface) (pc : GoInterface) :
    dialOk ds rb → dialOk (ds ++ [.perRPCCreds pc]) rb := by
  intro ⟨h2, h3⟩
  refine ⟨fun rbs h => h2 rbs ?_, List.mem_append_left _ h3⟩
  simpa using h

/-- **How `NewClient` finds the target's addresses** (persistent; grpc-trusted-T, T7, 2026-11-24): the
dial's one resolver `rb` (`dialOk`), which resolves the target's scheme `scheme` to `addrs`
(`grpcResolverAt`, taken), or grpc's `passthrough` resolver (`dialPassthrough`). -/
def dialTargetOk (ds : List GrpcDialOpt) (target : GoString) (rb : GoInterface) (scheme : GoString)
    (addrs : List GoString) : IProp GF :=
  iprop((⌜dialOk ds rb ∧ (scheme ++ go!"://") <+: target⌝ ∗ grpcResolverAt rb scheme addrs) ∨
    ⌜dialPassthrough ds target addrs⌝)

include hG in
/-- The raw fact behind `grpcConnOpts` (opaque, interim: made only by `grpc.NewClient`'s axiom; S2d's
proof of `NewClient` over the model defines it from the connection's `dopts`). Its signature carries
the heap's instance, which that definition will need. -/
opaque grpcConnOptsRaw (conn : Loc) (d : GrpcConnOpts) : IProp GF := iprop(True)

/-- **The connection `conn` was dialed with the options `d`** (persistent; grpc-trusted-T, T7,
2026-11-24; `grpc.NewClient`'s post, `connOptsOf ds`, beside `grpcConn conn addrs (unaryIcsOf ds) …`):
its unary interceptors, its stream interceptor and its per-RPC credentials are `d`'s. Only
`NewClient` makes it, once per connection, so every such fact of `conn` names the options it was
dialed with. What `ClientConn.NewStream` states the attempt's metadata and errors from. -/
def grpcConnOpts (conn : Loc) (d : GrpcConnOpts) : IProp GF := iprop(□ grpcConnOptsRaw conn d)

instance grpcConnOpts_persistent (conn : Loc) (d : GrpcConnOpts) :
    Persistent (grpcConnOpts (GF := GF) conn d) := by
  unfold grpcConnOpts; infer_instance

end defs2

end EtcdGrove
end Perennial
