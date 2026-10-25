/-
**The client's construction** (item 5, 2026-10-17; branch `construct`): the vocabulary of
`clientv3.New` (`client/v3/client.go`), down to the dial (`grpc.NewClient`,
`Proof/google_golang_org/grpc/InvDial.lean`). Lean-first (no Rocq counterpart).

**The configuration** (`clientCfgOk cfg eps`, the premise of `New`): the endpoints `eps`, at least
one, each plain (`host:port`: no `://`, not a `unix:`/`unixs:` socket, `plainEndpoint`), the
addresses servers are served at (several since 2026-10-21, `notes/decisions.md` D27: each attempt
goes to one of them); no TLS (`TLS` nil), no authentication (`Username`, `Password`, `Token` empty), no
context of the caller's (`Context` nil: the client's context is `context.TODO()`'s child), a
logger of the caller's (`Logger` non-nil: no default logger is built, `logutil`), the default call
options (`MaxCallSendMsgSize`, `MaxCallRecvMsgSize` not positive), no dial options of the caller's (`DialOptions` empty:
`issues/nonissues/etcd-client-dialoptions-unary-interceptor.md`, a `WithUnaryInterceptor` there would
replace the retry interceptor), no version check (`RejectOldCluster` false: `checkVersion`'s
`Status` calls) and no auto-sync (`AutoSyncInterval` zero: the `autoSync` goroutine returns at
once). `DialTimeout`, `MaxUnaryRetries`, `BackoffWaitBetween`, `BackoffJitterFraction` and
`PermitWithoutStream` are any, and so are the keepalive parameters (`DialKeepAliveTime`,
`DialKeepAliveTimeout`; since 2026-10-21, `notes/decisions.md` D28: a positive `DialKeepAliveTime`
adds grpc's keepalive option, `kaOpts`).

**The package's variables** (`clientNewVars`): `defaultCallOpts` (a full slice of grpc's scalar
call options, `callOptsAt`) and the retry defaults `defaultUnaryMaxRetries`,
`defaultBackoffWaitBetween`, `defaultBackoffJitterFraction`, never written: a premise until
package initialization (item 8) proves them part of `clientv3`'s fact.

**The resolver** (`etcdResolverOwn r eps`, exclusive, axiomatized): the client's
`*EtcdManualResolver` `r` (`internal/resolver`, names only), not yet dialed, with the endpoints
`eps`; `resolver.New` makes it, `SetEndpoints` sets them (axioms), and dialed with plain
endpoints it is grpc's resolver of the scheme `etcd-endpoints` to those addresses
(`etcdResolver_grpc`, an axiom: `Build`'s initial state is `state()`'s, one `resolver.Endpoint` per
endpoint at `endpoint.Interpret(ep)`, which is `ep` for a plain endpoint).

**What `New` gives** (`isNewClient cl ep V`): the `*Client` `cl` with its connection to the server
at `ep`, the client's (`clientKVAt`: `isEtcdConn`, the retry interceptor installed), its `KV` a
`*kv` over it (`kvObjAt`, what `client_*_end_to_end` take), its `Watcher` a watcher over it
(`isClientWatcherCore`, without the watch server's facts, D19f; `isNewClient_watcher` makes it
`isClientWatcher` given the facts of the server at `ep`, `watchAddrFacts V`), its logger
and the retry interceptor's reads (`retryClientOk`); `InvClientNewResult.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvDial
public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import GeneratedProof.go_etcd_io.etcd.client.v3.internal.endpoint
public import GeneratedProof.go_etcd_io.etcd.client.v3.internal.resolver
public import GeneratedProof.google_golang_org.grpc.credentials
public import GeneratedProof.google_golang_org.grpc.credentials.insecure
public import GeneratedProof.google_golang_org.grpc.keepalive
public import GeneratedProof.crypto.tls

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (backoffOk)

section pure
variable [ext : FfiSyntax]

/-- **A plain endpoint** (`host:port`): no `://` in it, and not a unix socket's (`unix:`,
`unixs:`); `endpoint.translateEndpoint` returns it unchanged, with `CredsOptional`. -/
def plainEndpoint (ep : GoString) : Prop :=
  ¬ (go!"://" <:+: ep) ∧ ¬ (go!"unix:" <+: ep) ∧ ¬ (go!"unixs:" <+: ep)

/-- **Plain endpoints** (D27, 2026-10-21: a client of several endpoints): at least one, each
plain. -/
def plainEndpoints (eps : List GoString) : Prop :=
  eps ≠ [] ∧ ∀ ep ∈ eps, plainEndpoint ep

theorem plainEndpoints_singleton (ep : GoString) : plainEndpoint ep → plainEndpoints [ep] := by
  intro h; exact ⟨List.cons_ne_nil _ _, fun e he => by simp at he; subst he; exact h⟩

/-- The scheme of etcd's manual resolver (`internal/resolver.Schema`). -/
def etcdScheme : GoString := go!"etcd-endpoints"

end pure

/-- **etcd's resolver `r`, not yet dialed, with the endpoints `eps`** (exclusive; an axiomatized
predicate; see the file header). -/
axiom etcdResolverOwn {GF : BundledGFunctors} [FfiSyntax] (r : Loc) (eps : List GoString) :
  IProp GF

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The resolver `r` as grpc's `resolver.Builder`. -/
abbrev resolverIface (r : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty)
    #r

/-- A field of a `*Client`. -/
abbrev clientF (cl : Loc) (f : GoString) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.Client f cl

end addrs

/-- **etcd's resolver, dialed with plain endpoints, resolves to them** (an axiom; see the file
header): `EtcdManualResolver.Build` sets the manual resolver's initial state to `state()`, one
endpoint per endpoint at `endpoint.Interpret(ep)` (`translateEndpoint`'s address: `ep` itself for
a plain one), with the round-robin service config (each attempt to one of them); its scheme is
`Schema`. One plain endpoint until 2026-10-21 (`notes/decisions.md` D27). -/
axiom etcdResolver_grpc {GF : BundledGFunctors} [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
    (r : Loc) (eps : List GoString) :
  plainEndpoints eps →
    (etcdResolverOwn (GF := GF) r eps ⊢ grpcResolverAt (resolverIface r) etcdScheme eps)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The package variables `New` reads** (persistent; see the file header). -/
def clientNewVars : IProp GF :=
  iprop((∃ sl : GoSlice,
      globalAddr go_etcd_io.etcd.client.v3.defaultCallOpts ↦□ sl ∗ callOptsAt sl) ∗
    (∃ n : w64, globalAddr go_etcd_io.etcd.client.v3.defaultUnaryMaxRetries ↦□ n) ∗
    (∃ d : time.Duration, globalAddr go_etcd_io.etcd.client.v3.defaultBackoffWaitBetween ↦□ d) ∗
    (∃ f : w64, globalAddr go_etcd_io.etcd.client.v3.defaultBackoffJitterFraction ↦□ f))

instance clientNewVars_persistent : Persistent (clientNewVars (GF := GF)) := by
  unfold clientNewVars; infer_instance

/-- Options holding only scalars are call options the client passes. -/
theorem callOptsOk_scalar (vs : List GoInterface) :
    ⌜∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ grpcScalarOptTys⌝ ⊢
      callOptsOk (GF := GF) vs := by
  induction vs with
  | nil => iintro -; unfold callOptsOk; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons v vs ih =>
    iintro %h
    unfold callOptsOk
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · unfold callOptOk; ileft; ipureintro; exact h v List.mem_cons_self
    · have ih' := ih; unfold callOptsOk at ih'
      iapply ih'; ipureintro; exact fun w hw => h w (List.mem_cons_of_mem _ hw)

/-- **`clientNewVars` is part of `client/v3`'s package facts** (`clientv3Init`; item 8, 2026-10-17:
until then a premise of `New` and its callees). -/
theorem clientNewVars_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ⊢ clientNewVars := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨-, -, ⟨%sl, %vs, #Hsl, #Hvs, %Hv⟩, #Hn, #Hd, #Hf, -⟩
  unfold clientNewVars
  iframe #
  unfold callOptsAt
  iexists vs
  iframe Hvs
  isplitr
  · ipureintro; exact Hv.1
  isplitl
  · iapply callOptsOk_scalar
    ipureintro
    exact Hv.2
  ipureintro
  exact Hv.2

/-- **What the client's API constructors read of a `*Client`** (persistent; `NewCluster`,
`NewLease`, `NewAuth`, `NewMaintenance`): non-nil, its logger, its connection, call options and
configuration, read-only. -/
def clientCoreAt (c : Loc) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗ isClientLogger c ∗ (∃ conn : Loc, clientF c go!"conn" ↦□ conn) ∗
    (∃ sl : GoSlice, clientF c go!"callOpts" ↦□ sl) ∗
    (∃ cfg : go_etcd_io.etcd.client.v3.Config, clientF c go!"cfg" ↦□ cfg))

instance clientCoreAt_persistent (c : Loc) : Persistent (clientCoreAt (GF := GF) c) := by
  unfold clientCoreAt; infer_instance

/-- **The keepalive option of a configuration's dial** (D28): grpc's `WithKeepaliveParams` when
`DialKeepAliveTime` is positive (`dialSetupOpts`), none otherwise. -/
def kaOpts (cfg : go_etcd_io.etcd.client.v3.Config) : List GrpcDialOpt :=
  if 0 < sint.Z cfg.DialKeepAliveTime' then [.keepalive] else []

/-- The keepalive option sets no unary interceptor. -/
theorem unaryIcsOf_kaOpts (cfg : go_etcd_io.etcd.client.v3.Config) (ds : List GrpcDialOpt) :
    unaryIcsOf (kaOpts cfg ++ ds) = unaryIcsOf ds := by
  unfold kaOpts
  split
  · exact unaryIcsOf_keepalive ds
  · rfl

/-- The keepalive option keeps a dial `NewClient`'s. -/
theorem dialOk_kaOpts (cfg : go_etcd_io.etcd.client.v3.Config) (ds : List GrpcDialOpt)
    (rb : GoInterface) : dialOk ds rb → dialOk (kaOpts cfg ++ ds) rb := by
  unfold kaOpts
  split
  · exact dialOk_keepalive ds rb
  · exact id

/-- **`New`'s configuration premise** (persistent; see the file header): the configuration `cfg`
of one plain endpoint `ep`. -/
def clientCfgOk (cfg : go_etcd_io.etcd.client.v3.Config) (eps : List GoString) : IProp GF :=
  iprop(cfg.Endpoints' ↦*□ eps ∗ cfg.DialOptions' ↦*□ ([] : List GoInterface) ∗
    ⌜plainEndpoints eps ∧ cfg.TLS' = null ∧ cfg.Username' = [] ∧ cfg.Password' = [] ∧
      cfg.Token' = [] ∧ cfg.Context' = GoInterface.nil ∧ cfg.Logger' ≠ null ∧
      sint.Z cfg.MaxCallSendMsgSize' ≤ 0 ∧ sint.Z cfg.MaxCallRecvMsgSize' ≤ 0 ∧
      cfg.RejectOldCluster' = false ∧
      cfg.AutoSyncInterval' = W64 0 ∧
      cfg.ChannelKeys' = slice.nil⌝)

instance clientCfgOk_persistent (cfg : go_etcd_io.etcd.client.v3.Config) (eps : List GoString) :
    Persistent (clientCfgOk (GF := GF) cfg eps) := by
  unfold clientCfgOk; infer_instance

end defs

end EtcdGrove
end Perennial
