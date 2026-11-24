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
  return to the attempts is `connCredsOk` (`NewClient`'s post, since the auth plan's C1);
* `.noProxy` (`WithNoProxy()`: sets `dopts.useProxy` to `false`, since 2026-11-24,
  `notes/putget-dist-plan.md` §12, finding F1; etcdstart's `NewClients` passes it): it sets no
  interceptor, no resolver and no credentials; at run time the connection dials each resolved
  address itself, never through an HTTP `CONNECT` proxy named by the process environment
  (`HTTPS_PROXY` or `https_proxy`), which grpc-go's delegating resolver reads otherwise. The model (`models/grpc`) reads no
  proxy variable, so `NewClient`'s axiom says the same of a dial with or without it.
An option a descriptor does not describe (`WithChainUnaryInterceptor`, `WithDefaultCallOptions`,
...) has no descriptor: a dial that holds one is not covered
(`clientv3.New`'s premises exclude `Config.DialOptions`,
`nonissues/etcd-client-dialoptions-unary-interceptor.md`).

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
  | noProxy

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

/-- No-proxy options set no unary interceptor. -/
theorem unaryIcsOf_noProxy (ds : List GrpcDialOpt) (n : Nat) :
    unaryIcsOf (ds ++ List.replicate n .noProxy) = unaryIcsOf ds := by
  unfold unaryIcsOf
  have h : (List.replicate n GrpcDialOpt.noProxy).filterMap GrpcDialOpt.unaryOf = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, List.filterMap_cons, GrpcDialOpt.unaryOf, ih]
  simp [List.filterMap_append, h]

/-- No-proxy options add no per-RPC credentials. -/
theorem credsOfDial_noProxy (n : Nat) : credsOfDial (List.replicate n .noProxy) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, GrpcDialOpt.credsOf, ih]

/-- Per-RPC credentials set no unary interceptor. -/
theorem unaryIcsOf_perRPCCreds (ds : List GrpcDialOpt) (pc : GoInterface) :
    unaryIcsOf (ds ++ [.perRPCCreds pc]) = unaryIcsOf ds := by
  unfold unaryIcsOf
  simp [List.filterMap_append, GrpcDialOpt.unaryOf]

end defs

/-- **`si` is etcd's client stream interceptor** (an axiomatized property: introduced only by the
client's `streamClientInterceptor` axiom; what grpc's `ClientConn.NewStream` axiom assumes of a
connection's stream interceptor). -/
axiom etcdStreamInterceptor [GooseExts] (si : GoFunc) : Prop

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

/-- What an interceptor option sets (`unaryInt`, `streamInt`), and what `WithNoProxy` sets
(`useProxy` false); nothing for the other descriptors. -/
def dialOptSets (d : GrpcDialOpt) (o' : google_golang_org.grpc.dialOptions) : Prop :=
  match d with
  | .unaryInterceptor ic => o'.unaryInt' = ic
  | .streamInterceptor ic => o'.streamInt' = ic
  | .noProxy => o'.useProxy' = false
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

/-- **A dial `NewClient` connects with** (pure): its stream interceptors are etcd's, and there is
one (G2, 2026-10-30: `NewStream`'s post states the metadata etcd's interceptor's `withVersion`
adds, false on a connection with no stream interceptor), and its one resolver is `rb` (every
`WithResolvers` of the dial gives `rb` alone, and one does). -/
def dialOk (ds : List GrpcDialOpt) (rb : GoInterface) : Prop :=
  (∀ si, GrpcDialOpt.streamInterceptor si ∈ ds → etcdStreamInterceptor si) ∧
    (∀ rbs, GrpcDialOpt.resolvers rbs ∈ ds → rbs = [rb]) ∧ GrpcDialOpt.resolvers [rb] ∈ ds ∧
    ∃ si, GrpcDialOpt.streamInterceptor si ∈ ds


/-- Keepalive sets no stream interceptor and no resolver: a dial with it is `NewClient`'s if the
dial without it is. -/
theorem dialOk_keepalive (ds : List GrpcDialOpt) (rb : GoInterface) :
    dialOk ds rb → dialOk (.keepalive :: ds) rb := by
  intro ⟨h1, h2, h3, si, h4⟩
  refine ⟨fun si h => h1 si ?_, fun rbs h => h2 rbs ?_, List.mem_cons_of_mem _ h3,
    si, List.mem_cons_of_mem _ h4⟩
  · simpa using h
  · simpa using h

/-- Per-RPC credentials set no stream interceptor and no resolver: a dial with them is
`NewClient`'s if the dial without them is. -/
theorem dialOk_perRPCCreds (ds : List GrpcDialOpt) (rb : GoInterface) (pc : GoInterface) :
    dialOk ds rb → dialOk (ds ++ [.perRPCCreds pc]) rb := by
  intro ⟨h1, h2, h3, si, h4⟩
  refine ⟨fun si h => h1 si ?_, fun rbs h => h2 rbs ?_, List.mem_append_left _ h3,
    si, List.mem_append_left _ h4⟩
  · simpa using h
  · simpa using h

/-- No-proxy options set no stream interceptor and no resolver: a dial with them is
`NewClient`'s if the dial without them is. -/
theorem dialOk_noProxy (ds : List GrpcDialOpt) (rb : GoInterface) (n : Nat) :
    dialOk ds rb → dialOk (ds ++ List.replicate n .noProxy) rb := by
  intro ⟨h1, h2, h3, si, h4⟩
  refine ⟨fun si h => h1 si ?_, fun rbs h => h2 rbs ?_, List.mem_append_left _ h3,
    si, List.mem_append_left _ h4⟩
  · rcases List.mem_append.1 h with h | h
    · exact h
    · exact absurd (List.eq_of_mem_replicate h) (by simp)
  · rcases List.mem_append.1 h with h | h
    · exact h
    · exact absurd (List.eq_of_mem_replicate h) (by simp)

/-- **The slice `sl` of `WithNoProxy()`'s options, read-only** (persistent; none or more): the
dial options a configuration of `clientv3.New` may carry (`clientCfgOk`). -/
def noProxyOptsAt (sl : GoSlice) (n : Nat) : IProp GF :=
  dialOptsAt sl (List.replicate n .noProxy)

instance noProxyOptsAt_persistent (sl : GoSlice) (n : Nat) :
    Persistent (noProxyOptsAt (GF := GF) sl n) := by
  unfold noProxyOptsAt; infer_instance

/-- The nil slice holds no option. -/
theorem noProxyOptsAt_nil : ⊢ noProxyOptsAt (GF := GF) slice.nil 0 := by
  unfold noProxyOptsAt dialOptsAt
  iexists ([] : List GoInterface)
  isplitl
  · iapply ownSlice_nil
  · simp only [List.replicate_zero]
    iapply BigSepL2.bigSepL2_nil.2
    itrivial

end defs2

end EtcdGrove
end Perennial
