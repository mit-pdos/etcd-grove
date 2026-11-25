/-
**grpc's server, built and started** (item 4 of the client→server path, 2026-10-17; Lean-first,
no Rocq counterpart; restated in per-type stage B, B1b): what produces Go's configuration of a
server, which `grpc.start'` (`InvGrpcRun.lean`) turns into the address's service table and the facts
`grpcServerAt` and `isGrpcStreamMd`. The Go-level specs of grpc's `NewServer`, its options,
`Server.RegisterService` and `Server.Serve`, and of `net.Listen`, are trust-boundary axioms
(`Spec/google_golang_org/grpc/`, `Spec/net/Listen.lean`); this file is their vocabulary.

**Options** (`grpcSrvOpt v k`, persistent, a definition since phase 7 S1, 2026-11-21: `v` is grpc's
`*funcServerOption` whose closure does `k` to the `serverOptions`, `srvOptFnOk`; introduced by the
option constructors' specs, six of them proved over the model's bodies): what `NewServer` does with
it, `k`:
* `.chainUnary ics` (`ChainUnaryInterceptor(ics...)`): the unary interceptors `ics`, appended to
  the server's chain in order (grpc's `chainUnaryServerInterceptors`; no `UnaryInterceptor`
  option is specified, so the chain is these lists, concatenated);
* `.chainStream ics` (`ChainStreamInterceptor(ics...)`): likewise for streams;
* `.stats h` (`StatsHandler(h)`, of a handler with `grpcStatsHandlerOk`: otelgrpc's): `h` added to
  the server's stats handlers; it adds no value under etcd's context keys (`grpcRunCtx`);
* `.neutral`: an option that does not change which handler runs for a method, nor what a run is
  given (the run's context, `grpcRunCtx`; the decoded request, `grpcDecOk`), nor how requests are
  decoded: it changes only the fields of a whitelist (`srvOptsSameBut`: message size limits, a call
  over the limit failing before its handler runs or its response not delivered, an error for the
  client; `MaxConcurrentStreams`, calls wait; flow-control windows, buffers, header limits,
  keepalive parameters and enforcement policy, the connection timeout, server workers, waiting for
  handlers), and the codec only to a protobuf codec's (`srvCodecOk`: `CustomCodec` of a codec with
  `grpcProtoCodec`, so the wire models `ProtoMsg` are protobuf's). Every other field stays: an
  option setting `UnaryInterceptor`/`StreamInterceptor`, credentials, a compressor, an unknown-service
  handler, a stream wrapper or a non-protobuf codec is of no kind (2026-11-26,
  `notes/axiom-review/grpc-neutral-narrow.md`: until then only the chains and the stats handlers
  were fixed, so the model's own `UnaryInterceptor(i)` was provably `.neutral` while `NewServer`
  chains `i` in front of every handler). The other kinds fix the same fields.

**The server being built** (`grpcSrvNew gs ics sics svcs regs sregs`, exclusive; W1, 2026-11-26, a
definition over the model's `Server` struct, until then axiomatized):
`NewServer`'s `*grpc.Server` `gs`, not serving yet, with the unary and stream chains `ics`,
`sics`, the services `svcs` registered (their names), and their unary methods `regs` and streams
`sregs` (full method name `/<service>/<method>`, `MethodDesc.Handler`/`StreamDesc.Handler`,
service value). `RegisterService` adds a service (`grpcDescIs`: its `ServiceDesc`, read-only; a
service name not registered yet, a service value implementing the descriptor's `HandlerType`:
grpc's `logger.Fatalf` otherwise; its method and stream names distinct, and every stream descriptor
setting `ClientStreams` or `ServerStreams`: premises stronger than grpc checks, which registers equal
method and stream names, the unary one winning (test T9b), and runs an unflagged stream's handler
without the stream interceptor, `server.go:1446-1450` (test T10b)).

**The start** (`grpc.start'`, a theorem in `InvGrpcRun.lean`): the server being built, whose
full method and stream names are jointly distinct, and a listener bound at `addr` (`netListenerAt`,
`Proof/net/InvNet.lean`) with what `Listen` left, set `addr`'s service table to Go's configuration, and
give the right to serve it (`grpcServeTok gs lis addr Svc`, what `gs.Serve(lis)` takes). A ghost step,
before the `go gs.Serve(lis)`: the server's methods are served at `addr` once `Serve` runs (a call
before `Serve` accepts waits, or fails: an error for the client). After it the server can no longer
register a service (grpc's `RegisterService` after `Serve` is fatal).

**The replies' size** (`grpcRepliesFit`, a premise of `grpc.start'`, 2026-10-31,
`notes/reply-size.md`): grpc marshals a reply before any size check, and the codec's `make` panics
above Go's `maxAlloc` (`grpcReplyMax`). The start takes the named workload premise that no reply of
the run (the replies to the program's own clients' calls) exceeds it; the facts it makes exist only
in such a run, so the trusted `Serve` model's leaves (`respond`'s size claim), reached through
`grpcServeTok`, are true under it, and so is every result built on them (the served results
`etcd_kv_served`, `ServedOn`, `AuthnServedOn`, v3rpc's, whose statements do not show it). The token
yields `grpcRepliesFit` or, since T9, `grpcRepliesBounded` (a disjunct of `grpcServeTok`), which holds wherever the token is made:
it is `grpc.start'`'s premise.

The health server (`grpcHealthSrv`), grpc-prometheus's server metrics (`promSrvMetrics`) and the
stats handlers' property (`grpcStatsHandlerOk`) are in `InvGrpcHealth.lean`, `InvGrpcProm.lean` and
`InvGrpcStats.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.net.InvNet
public import Perennial.Proof.sync.CondDefs
public import GeneratedProof.google_golang_org.grpc.internal.stats
public import GeneratedProof.google_golang_org.grpc.internal.grpcsync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **What `grpc.NewServer` does with an option** (see the file header). -/
inductive SrvOptKind [GooseExts] : Type where
  | chainUnary (ics : List GoFunc)
  | chainStream (ics : List GoFunc)
  | stats (h : GoInterface)
  | neutral

/-- The unary interceptors an option adds to the chain. -/
def SrvOptKind.unary [GooseExts] : SrvOptKind → List GoFunc
  | .chainUnary ics => ics
  | _ => []

/-- The stream interceptors an option adds to the chain. -/
def SrvOptKind.stream [GooseExts] : SrvOptKind → List GoFunc
  | .chainStream ics => ics
  | _ => []

/-- The unary chain of a server built with options of the kinds `ks`. -/
def srvOptsUnary [GooseExts] (ks : List SrvOptKind) : List GoFunc := ks.flatMap SrvOptKind.unary

/-- The stream chain of a server built with options of the kinds `ks`. -/
def srvOptsStream [GooseExts] (ks : List SrvOptKind) : List GoFunc := ks.flatMap SrvOptKind.stream

/-- **The `grpc.Codec` `c` is a protobuf codec** (an axiomatized property): its `Marshal` and
`Unmarshal` are protobuf's (`proto.Marshal`/`proto.Unmarshal` of the message), as the default
codec's; what the wire models (`ProtoMsg`) presume. etcd's `v3rpc.codec` is one
(`v3rpc.codec_proto`). -/
axiom grpcProtoCodec [GooseExts] (c : GoInterface) : Prop

/-- **The server being built, bound to the listener `lis` at `addr`** (exclusive), as certified by
`etcd_noRefusal`/`etcd_noOtherRefusal`; intended reading `grpcSrvNew gs … ∗ netListenerAt lis addr`;
consumed only by `grpc.startBound`, inside `grpcServeTok`. It covers only the server certified at the
listener it was certified with, the FIRST server at `addr`: the certificate `noRefusalAt addr` is a
fact about the address string and outlives that listener. Once the listener is closed (a synchronous
`Serve` returning on an `Accept` failure, a crash) or on another node, a new listener at `addr`
(`listen_au` from `grpcAddrAt`) can host a server that refuses while `noRefusalAt addr` still holds
(`notes/axiom-review/phase7-switch.md`, finding 1). Interim: retired by decision E (no-refusal a
property of the table's entries). -/
axiom grpcSrvAtLis {GF : BundledGFunctors} [GooseExts] (gs : Loc) (lis : GoInterface) (addr : GoString)
  (ics sics : List GoFunc) (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface)) :
  IProp GF

section pure
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- A method's full name, as grpc's server dispatches it (`/<service>/<method>`). -/
def grpcFullName (sn mn : GoString) : GoString := go!"/" ++ sn ++ go!"/" ++ mn

/-- The unary methods a `ServiceDesc` with the service name `sn` and the methods `mds` registers,
for the service value `ss`. -/
def descRegs (sn : GoString) (mds : List google_golang_org.grpc.MethodDesc) (ss : GoInterface) :
    List (GoString × GoFunc × GoInterface) :=
  mds.map fun md => (grpcFullName sn md.MethodName', md.Handler', ss)

/-- The streams a `ServiceDesc` with the service name `sn` and the streams `sds` registers, for
the service value `ss`. -/
def descSRegs (sn : GoString) (sds : List google_golang_org.grpc.StreamDesc) (ss : GoInterface) :
    List (GoString × GoFunc × GoInterface) :=
  sds.map fun sd => (grpcFullName sn sd.StreamName', sd.Handler', ss)

/-- The method and stream names of a `ServiceDesc`. -/
def descNames (mds : List google_golang_org.grpc.MethodDesc)
    (sds : List google_golang_org.grpc.StreamDesc) : List GoString :=
  mds.map (·.MethodName') ++ sds.map (·.StreamName')

theorem grpc_sep_inj {α : Type} (c : α) : ∀ (a a' b b' : List α), c ∉ a → c ∉ a' →
    a ++ c :: b = a' ++ c :: b' → a = a' ∧ b = b'
  | [], [], b, b', _, _, h => by simpa using h
  | [], x :: a', b, b', _, h2, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h2
  | x :: a, [], b, b', h1, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1.symm ▸ List.mem_cons_self) h1
  | x :: a, y :: a', b, b', h1, h2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := grpc_sep_inj c a a' b b' (fun hm => h1 (List.mem_cons_of_mem _ hm))
      (fun hm => h2 (List.mem_cons_of_mem _ hm)) h
    exact ⟨by rw [this.1], this.2⟩

theorem grpc_go_slash : (go!"/" : GoString) = [(47 : w8)] := rfl

/-- **Slash-free service names are recovered from full names** (`grpcFullName sn mn =
"/" ++ sn ++ "/" ++ mn`): what separates the services of `v3rpc.Server` in B2's joint `Nodup`. -/
theorem grpcFullName_inj (sn sn' mn mn' : GoString) (h1 : (47 : w8) ∉ sn) (h2 : (47 : w8) ∉ sn')
    (h : grpcFullName sn mn = grpcFullName sn' mn') : sn = sn' ∧ mn = mn' := by
  unfold grpcFullName at h
  rw [grpc_go_slash] at h
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, true_and] at h
  exact grpc_sep_inj (47 : w8) sn sn' mn mn' h1 h2 h


theorem grpc_nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α),
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, grpc_nodup_map_on f l
      (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hnd.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact hnd.1 (hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb ▸ hb)

/-- The full names of services: service `s.1`'s methods `s.2.1` and streams `s.2.2`. -/
def grpcNames (S : List (GoString × List GoString × List GoString)) : List GoString :=
  S.flatMap fun s => (s.2.1 ++ s.2.2).map (grpcFullName s.1)

/-- Distinct slash-free services with per-service distinct names have distinct full names. -/
theorem grpcNames_nodup (S : List (GoString × List GoString × List GoString))
    (hS : ∀ s ∈ S, (47 : w8) ∉ s.1 ∧ (s.2.1 ++ s.2.2).Nodup) (hsn : (S.map (·.1)).Nodup) :
    (grpcNames S).Nodup := by
  induction S with
  | nil => simp [grpcNames]
  | cons s S ih =>
    simp only [grpcNames, List.flatMap_cons, List.map_cons, List.nodup_cons] at hsn ⊢
    have hs := hS s List.mem_cons_self
    refine List.nodup_append.mpr ⟨?_, ih (fun t ht => hS t (List.mem_cons_of_mem _ ht)) hsn.2, ?_⟩
    · refine grpc_nodup_map_on _ _ ?_ hs.2
      intro x _ y _ hxy
      exact (grpcFullName_inj s.1 s.1 x y hs.1 hs.1 hxy).2
    · intro a ha b hb hab
      subst hab
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨t, ht, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
      have := (grpcFullName_inj s.1 t.1 x y hs.1 (hS t (List.mem_cons_of_mem _ ht)).1 hy.symm).1
      exact hsn.1 (this ▸ List.mem_map_of_mem ht)

theorem descRegs_names (sn : GoString) (mds : List google_golang_org.grpc.MethodDesc)
    (ss : GoInterface) :
    (descRegs sn mds ss).map Prod.fst = (mds.map (·.MethodName')).map (grpcFullName sn) := by
  simp [descRegs, List.map_map, Function.comp_def]

theorem descSRegs_names (sn : GoString) (sds : List google_golang_org.grpc.StreamDesc)
    (ss : GoInterface) :
    (descSRegs sn sds ss).map Prod.fst = (sds.map (·.StreamName')).map (grpcFullName sn) := by
  simp [descSRegs, List.map_map, Function.comp_def]

/-- **The service value `ss` implements the handler type `ht`** (grpc's `RegisterService` check,
`reflect.TypeOf(ss).Implements(reflect.TypeOf(ht).Elem())`): `ht` is a nil pointer to an
interface type `T` (the generated `(*KVServer)(nil)`), `ss` a non-nil value whose type is in
`T`'s type set. -/
def grpcImplements (ss ht : GoInterface) : Prop :=
  ∃ (T : go.GoType) (si : GoInterfaceOk),
    ht = interface.mkOk (go.GoType.PointerType T) #(null : Loc) ∧ ss = GoInterface.ok si ∧
    go.typeSetContains si.ty T = true

/-- The interface `interface{ testEmbeddedByValue() }` the generated `Register*Server` assert a
service value to (it calls the method if the value embeds the `Unimplemented*Server` by value).
The method is unexported, so its id is qualified by the package that declares it, `etcdserverpb`
(Go's `go/types.Id`, as goose names it). -/
def testEmbeddedIface : go.GoType :=
  go.GoType.InterfaceType [go.InterfaceElem.MethodElem
    go!"go.etcd.io/etcd/api/v3/etcdserverpb.testEmbeddedByValue"
    (go.signature.Signature [] false [])]

/-- **The service value `ss` has no `testEmbeddedByValue`** (a method-set fact: etcd's services
embed the `Unsafe*Server` interfaces, not `Unimplemented*Server` by value): the generated
`Register*Server`'s type assertion fails and it calls nothing. -/
def grpcNoTestEmbedded (ss : GoInterface) : Prop :=
  ∃ si : GoInterfaceOk, ss = GoInterface.ok si ∧ go.typeSetContains si.ty testEmbeddedIface = false

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`so'` is `so` but for the fields no handler, run context or decoding depends on**, and for
the codec, the two interceptor chains and the stats handlers, which each option kind's clause of
`srvOptFnOk` states (2026-11-26, `notes/axiom-review/grpc-neutral-narrow.md`). The whitelist, of
grpc-go v1.84's `serverOptions` (`models/grpc/server.go`): the stream limit, the message size limits,
the keepalive parameters and enforcement policy, the flow-control windows (`initialWindowSize`,
`initialConnWindowSize`, `staticWindowSize`), the transport's buffers (`writeBufferSize`,
`readBufferSize`, `sharedWriteBuffer`), the connection timeout, the header limits
(`maxHeaderListSize`, `headerTableSize`), the server workers (`numServerWorkers`, which run the same
`handleStream`; the model has none) and `waitForHandlers` (read by `Stop` only). Every other field
(`creds`, `cp`, `dc`, `unaryInt`, `streamInt`, `unknownStreamDesc`, `streamWrapper`, and any field
grpc adds) is `so`'s. -/
def srvOptsSameBut (so so' : google_golang_org.grpc.serverOptions) : Prop :=
  so' = { so with
    codec' := so'.codec', chainUnaryInts' := so'.chainUnaryInts',
    chainStreamInts' := so'.chainStreamInts', statsHandlers' := so'.statsHandlers',
    maxConcurrentStreams' := so'.maxConcurrentStreams',
    maxReceiveMessageSize' := so'.maxReceiveMessageSize',
    maxSendMessageSize' := so'.maxSendMessageSize',
    keepaliveParams' := so'.keepaliveParams', keepalivePolicy' := so'.keepalivePolicy',
    initialWindowSize' := so'.initialWindowSize',
    initialConnWindowSize' := so'.initialConnWindowSize',
    writeBufferSize' := so'.writeBufferSize', readBufferSize' := so'.readBufferSize',
    sharedWriteBuffer' := so'.sharedWriteBuffer', connectionTimeout' := so'.connectionTimeout',
    maxHeaderListSize' := so'.maxHeaderListSize', headerTableSize' := so'.headerTableSize',
    numServerWorkers' := so'.numServerWorkers', waitForHandlers' := so'.waitForHandlers',
    staticWindowSize' := so'.staticWindowSize' }

/-- **The codec of `so'` is `so`'s, or a protobuf codec's**: `CustomCodec(c)` of a codec with
`grpcProtoCodec c` stores `newCodecV0Bridge(c)`, the value `codecV0Bridge{codec: c}` (as `any`),
whose `Marshal`/`Unmarshal` are `c`'s (`models/grpc/codec.go`). -/
def srvCodecOk (so so' : google_golang_org.grpc.serverOptions) : Prop :=
  so'.codec' = so.codec' ∨ ∃ c : GoInterface, grpcProtoCodec c ∧
    so'.codec' = interface.mkOk google_golang_org.grpc.codecV0Bridge.ty
      #(google_golang_org.grpc.codecV0Bridge.mk c)

/-- **What the closure `f` of a server option of the kind `k` does to `*serverOptions`**
(persistent; phase 7 S1, `notes/phase7-plan.md`: grpc is the model's, `models/grpc`): applied to a
`p ↦ so`, it returns with `p ↦ so'`, where `so'` is `so` but for the whitelisted fields
(`srvOptsSameBut`) and
* `.neutral`: the unary and stream chains and the stats handlers are `so`'s, the codec is `so`'s or a
  protobuf codec's (`srvCodecOk`);
* `.chainUnary ics` (`.chainStream ics`): the chain, whose elements `us` and capacity it is given,
  is `us ++ ics` (`append(o.chainUnaryInts, interceptors...)`), the other chain, the stats
  handlers and the codec are `so`'s;
* `.stats h`: the stats handlers, whose elements `hs` and capacity it is given, are `hs ++ [h]` if
  `h` is not nil, `hs` if it is (grpc logs and ignores a nil handler), the chains and the codec are
  `so`'s.
The ownership each kind is given is what its closure reads and writes, so that `NewServer`, which
applies the options in order to one `serverOptions`, can hold it. -/
def srvOptFnOk (f : GoFunc) : SrvOptKind → IProp GF
  | .neutral => iprop(□ ∀ (p : Loc) (so : google_golang_org.grpc.serverOptions)
      (Φ : val → IProp GF),
      p ↦ so -∗ ▷ (∀ so' : google_golang_org.grpc.serverOptions, p ↦ so' -∗
        ⌜srvOptsSameBut so so' ∧ srvCodecOk so so' ∧ so'.chainUnaryInts' = so.chainUnaryInts' ∧
          so'.chainStreamInts' = so.chainStreamInts' ∧ so'.statsHandlers' = so.statsHandlers'⌝ -∗
        Φ #()) -∗
      WP (App (Val #f) (Val #p)) {{ Φ }})
  | .chainUnary ics => iprop(□ ∀ (p : Loc) (so : google_golang_org.grpc.serverOptions)
      (us : List GoFunc) (Φ : val → IProp GF),
      p ↦ so -∗ so.chainUnaryInts' ↦* us -∗ ownSliceCap GoFunc so.chainUnaryInts' (DFrac.own 1) -∗
      ▷ (∀ so' : google_golang_org.grpc.serverOptions, p ↦ so' -∗
        so'.chainUnaryInts' ↦* (us ++ ics) -∗ ownSliceCap GoFunc so'.chainUnaryInts' (DFrac.own 1) -∗
        ⌜srvOptsSameBut so so' ∧ so'.codec' = so.codec' ∧ so'.chainStreamInts' = so.chainStreamInts' ∧
          so'.statsHandlers' = so.statsHandlers'⌝ -∗
        Φ #()) -∗
      WP (App (Val #f) (Val #p)) {{ Φ }})
  | .chainStream ics => iprop(□ ∀ (p : Loc) (so : google_golang_org.grpc.serverOptions)
      (us : List GoFunc) (Φ : val → IProp GF),
      p ↦ so -∗ so.chainStreamInts' ↦* us -∗ ownSliceCap GoFunc so.chainStreamInts' (DFrac.own 1) -∗
      ▷ (∀ so' : google_golang_org.grpc.serverOptions, p ↦ so' -∗
        so'.chainStreamInts' ↦* (us ++ ics) -∗ ownSliceCap GoFunc so'.chainStreamInts' (DFrac.own 1) -∗
        ⌜srvOptsSameBut so so' ∧ so'.codec' = so.codec' ∧ so'.chainUnaryInts' = so.chainUnaryInts' ∧
          so'.statsHandlers' = so.statsHandlers'⌝ -∗
        Φ #()) -∗
      WP (App (Val #f) (Val #p)) {{ Φ }})
  | .stats h => iprop(□ ∀ (p : Loc) (so : google_golang_org.grpc.serverOptions)
      (hs : List GoInterface) (Φ : val → IProp GF),
      p ↦ so -∗ so.statsHandlers' ↦* hs -∗ ownSliceCap GoInterface so.statsHandlers' (DFrac.own 1) -∗
      ▷ (∀ so' : google_golang_org.grpc.serverOptions, p ↦ so' -∗
        so'.statsHandlers' ↦* (hs ++ (if h = interface.nil then [] else [h])) -∗
        ownSliceCap GoInterface so'.statsHandlers' (DFrac.own 1) -∗
        ⌜srvOptsSameBut so so' ∧ so'.codec' = so.codec' ∧ so'.chainUnaryInts' = so.chainUnaryInts' ∧
          so'.chainStreamInts' = so.chainStreamInts'⌝ -∗
        Φ #()) -∗
      WP (App (Val #f) (Val #p)) {{ Φ }})

instance srvOptFnOk_persistent (f : GoFunc) (k : SrvOptKind) :
    Persistent (srvOptFnOk (GF := GF) f k) := by
  cases k <;> unfold srvOptFnOk <;> infer_instance

/-- **The `grpc.ServerOption` `v` is an option of the kind `k`** (persistent; see the file header):
grpc's `*funcServerOption` (the only `ServerOption` the specified constructors return), read-only,
whose closure does `k` (`srvOptFnOk`). -/
def grpcSrvOpt (v : GoInterface) (k : SrvOptKind) : IProp GF :=
  iprop(∃ (l : Loc) (f : GoFunc),
    ⌜v = interface.mkOk (go.GoType.PointerType google_golang_org.grpc.funcServerOption.ty) #l⌝ ∗
    l ↦□ google_golang_org.grpc.funcServerOption.mk f ∗ srvOptFnOk f k)

instance grpcSrvOpt_persistent (v : GoInterface) (k : SrvOptKind) :
    Persistent (grpcSrvOpt (GF := GF) v k) := by
  unfold grpcSrvOpt; infer_instance

/-- **The `*grpc.ServiceDesc` `sd`** (persistent, read-only): its service name `sn`, its handler
type `ht`, its methods `mds` and its streams `sds`. -/
def grpcDescIs (sd : Loc) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc) :
    IProp GF :=
  iprop(∃ msl ssl : GoSlice,
    structFieldRef google_golang_org.grpc.ServiceDesc go!"ServiceName" sd ↦□ sn ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"HandlerType" sd ↦□ ht ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Methods" sd ↦□ msl ∗ msl ↦*□ mds ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams" sd ↦□ ssl ∗ ssl ↦*□ sds ∗
    ∃ md : GoInterface, structFieldRef google_golang_org.grpc.ServiceDesc go!"Metadata" sd ↦□ md)

instance grpcDescIs_persistent (sd : Loc) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc) :
    Persistent (grpcDescIs (GF := GF) sd sn ht mds sds) := by
  unfold grpcDescIs; infer_instance

/-! ### The server being built (W1, 2026-11-26: a definition, until then the axiom `grpcSrvNew`;
`notes/axiom-review/phase7-w1.md` §3) -/

/-- **The closure `wrapUnaryHandler(md)` returns** (`server.go:1165`), over the cells `sl` (its
receiver `s`) and `mdl` (its `md`): the generated body's function literal, its two captured
variables substituted, exactly the value Go builds (the lead's option (a), W1 §3.1). -/
noncomputable def wrapUnaryLam : Expr :=
  match google_golang_org.grpc.Server.wrapUnaryHandler.impl with
  | .RecV _ _ (.Rec _ _ (.App (.Rec _ _ (.App (.Rec _ _ _) (.App _ (.App (.Rec _ _
      (.App (.Rec _ _ (.App (.Rec _ _ _) lam)) _)) _)))) _)) => lam
  | _ => .Val (.LitV .LitPoison)

noncomputable def wrapUnaryClosure (sl mdl : Loc) : GoFunc :=
  match subst "md" #mdl (subst "s" #sl wrapUnaryLam) with
  | .Rec f x e => func.mk f x e
  | _ => func.nil

/-- The function literal `chainUnaryInterceptors(interceptors)` returns (`server.go:1112`). -/
noncomputable def chainUnaryLam : Expr :=
  match google_golang_org.grpc.chainUnaryInterceptors.impl with
  | .RecV _ _ (.App (.Rec _ _ (.App (.Rec _ _ _) (.App _ (.App (.Rec _ _
      (.App (.Rec _ _ _) lam)) _)))) _) => lam
  | _ => .Val (.LitV .LitPoison)

/-- **The chained unary interceptor over the cell `il`** (holding the chain's slice). -/
noncomputable def chainUnaryClosure (il : Loc) : GoFunc :=
  match subst "interceptors" #il chainUnaryLam with
  | .Rec f x e => func.mk f x e
  | _ => func.nil

/-- The function literal `chainStreamInterceptors(interceptors)` returns. -/
noncomputable def chainStreamLam : Expr :=
  match google_golang_org.grpc.chainStreamInterceptors.impl with
  | .RecV _ _ (.App (.Rec _ _ (.App (.Rec _ _ _) (.App _ (.App (.Rec _ _
      (.App (.Rec _ _ _) lam)) _)))) _) => lam
  | _ => .Val (.LitV .LitPoison)

/-- **The chained stream interceptor over the cell `il`.** -/
noncomputable def chainStreamClosure (il : Loc) : GoFunc :=
  match subst "interceptors" #il chainStreamLam with
  | .Rec f x e => func.mk f x e
  | _ => func.nil

/-- **`v` is the interceptor `chain{Unary,Stream}ServerInterceptors` stores for the chain `ics`**
held read-only at `sl` (no single `UnaryInterceptor`/`StreamInterceptor` option is of any kind, so
none is prepended): `nil` for none, the one for one, else the chaining closure (`mk`) over a
read-only cell holding `sl`. -/
def srvChainIs (mk : Loc → GoFunc) (v : GoFunc) (sl : GoSlice) (ics : List GoFunc) : IProp GF :=
  iprop(sl ↦*□ ics ∗
    (⌜ics = [] ∧ v = zero_val GoFunc⌝ ∨ (∃ i, ⌜ics = [i] ∧ v = i⌝) ∨
      ∃ il : Loc, ⌜2 ≤ ics.length ∧ v = mk il⌝ ∗ il ↦□ sl))

/-- **`v` is the stats handler `istats.NewCombinedHandler(hs...)` returns** for the handlers `hs` held
read-only at `sl`, each with `grpcStatsHandlerOk` (`StatsHandler`'s premise, carried by `.stats`): `nil`
for none, the one for one, else a `*combinedHandler` holding `sl`. -/
def srvStatsIs (v : GoInterface) (sl : GoSlice) (hs : List GoInterface) : IProp GF :=
  iprop(sl ↦*□ hs ∗ ⌜∀ h ∈ hs, grpcStatsHandlerOk h⌝ ∗
    (⌜hs = [] ∧ v = GoInterface.nil⌝ ∨ (∃ h, ⌜hs = [h] ∧ v = h⌝) ∨
      ∃ l : Loc, ⌜2 ≤ hs.length ∧ v = interface.mkOk
          (go.GoType.PointerType google_golang_org.grpc.internal.stats.combinedHandler.ty) #l⌝ ∗
        l ↦□ google_golang_org.grpc.internal.stats.combinedHandler.mk sl))

/-- **A registered service** (one `RegisterService`): its descriptor `sd` (`grpcDescIs`), service name
`sn`, handler type `ht`, methods `mds`, streams `sds`, and service value `ss`. -/
structure GrpcSrvReg where
  sd : Loc
  sn : GoString
  ht : GoInterface
  mds : List google_golang_org.grpc.MethodDesc
  sds : List google_golang_org.grpc.StreamDesc
  ss : GoInterface

/-- **The `streams` map `register` builds for the descriptor with method and stream slices `msl`,
`ssl`**: each stream's name to its descriptor in `ssl` (`&sd.Streams[i]`), then each method's name to
the fresh descriptor `mls[j]` (`register`'s order; the names are distinct, `RegisterService`'s
premise). -/
def srvStreamsL (r : GrpcSrvReg) (ssl : GoSlice) (mls : List Loc) : List (GoString × Loc) :=
  (r.sds.zipIdx.map fun (d, i) =>
      (d.StreamName', sliceIndexRef google_golang_org.grpc.StreamDesc (i : Int) ssl)) ++
    (r.mds.zip mls).map fun (d, l) => (d.MethodName', l)

/-- **The registered service `r` at the `*serviceInfo` `il` of the server `gs`** (`register`,
`server.go:759-788`): its descriptor; `il` holds `r.ss`, a `streams` map with `srvStreamsL`'s
entries and the descriptor's `Metadata`; each method's descriptor `mls[j]`, read-only, is
`&StreamDesc{name, wrapUnaryHandler(&sd.Methods[j]), false, false}`: the closure over a read-only
cell holding `gs` and one holding `&sd.Methods[j]`. -/
def srvRegIs (gs : Loc) (r : GrpcSrvReg) (il : Loc) : IProp GF :=
  iprop(grpcDescIs r.sd r.sn r.ht r.mds r.sds ∗
    ∃ (msl ssl : GoSlice) (stm : Loc) (mdv : GoInterface) (mls : List Loc) (M2 : GMap GoString Loc),
      structFieldRef google_golang_org.grpc.ServiceDesc go!"Methods" r.sd ↦□ msl ∗
      structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams" r.sd ↦□ ssl ∗
      il ↦ google_golang_org.grpc.serviceInfo.mk r.ss stm mdv ∗
      ownMap stm (DFrac.own 1) M2 ∗
      ⌜mls.length = r.mds.length ∧ ∀ n, M2 !! n = map.lookupL n (srvStreamsL r ssl mls)⌝ ∗
      [∗list] j ↦ ml ∈ mls, ∃ (d : google_golang_org.grpc.MethodDesc) (cs cm : Loc),
        ⌜r.mds[j]? = some d⌝ ∗ cs ↦□ gs ∗
        cm ↦□ sliceIndexRef google_golang_org.grpc.MethodDesc (j : Int) msl ∗
        ml ↦□ google_golang_org.grpc.StreamDesc.mk d.MethodName' (wrapUnaryClosure cs cm) false false)

/-- **The `serverOptions` of a server built with the chains `ics`, `sics`** (`NewServer`, after
`chainUnaryServerInterceptors`/`chainStreamServerInterceptors`): the chains read-only, the stored
interceptors theirs (`srvChainIs`), the stats handlers `hs` (`srvStatsIs`, with the server's
`statsHandler` `sh`), no credentials, compressor, decompressor, unknown-stream handler or stream
wrapper, and the codec nil or a protobuf codec's (`srvCodecOk`'s form). -/
def srvOptsIs (so : google_golang_org.grpc.serverOptions) (sh : GoInterface) (ics sics : List GoFunc) :
    IProp GF :=
  iprop(srvChainIs chainUnaryClosure so.unaryInt' so.chainUnaryInts' ics ∗
    srvChainIs chainStreamClosure so.streamInt' so.chainStreamInts' sics ∗
    (∃ hs : List GoInterface, srvStatsIs sh so.statsHandlers' hs) ∗
    ⌜so.creds' = GoInterface.nil ∧ so.cp' = GoInterface.nil ∧ so.dc' = GoInterface.nil ∧
      so.unknownStreamDesc' = null ∧ so.streamWrapper' = zero_val GoFunc ∧
      (so.codec' = GoInterface.nil ∨ ∃ c : GoInterface, grpcProtoCodec c ∧
        so.codec' = interface.mkOk google_golang_org.grpc.codecV0Bridge.ty
          #(google_golang_org.grpc.codecV0Bridge.mk c))⌝)

/-- **A fresh `grpcsync.Event` at `q`** (`NewEvent`: `&Event{c: make(chan struct{})}`): not fired, its
channel unbuffered, open, idle, owned. -/
def srvEventIs (q : Loc) : IProp GF :=
  iprop(∃ (ch : Loc) (γ : ChanNames),
    q ↦ google_golang_org.grpc.internal.grpcsync.Event.mk (zero_val _) ch ∗
    isChan ch γ Unit ∗ ⌜γ.chanCap = W64 0⌝ ∗ ownChan γ Unit ChanState.Idle)

/-- **The server being built** (exclusive; see the file header; W1, 2026-11-26, a definition over the
model's `Server` struct, until then an axiom): `NewServer`'s `*grpc.Server` `gs` with the unary and
stream chains `ics`, `sics` (`srvOptsIs`), not serving (`serve`, `drain` false; no listener, no
connection), no event log, its `mu` a mutex (lock invariant `True`: the fields are this predicate's)
with `cv` a condition variable on it, fresh `quit`/`done` events and zero wait groups, and the
services `rs` registered in order: `svcs` their names, `regs`/`sregs` their methods' and streams'
full names with their handlers and service values (`descRegs`, `descSRegs`), `services` mapping each
name to its `*serviceInfo` (`srvRegIs`). **Invariant every producer upholds** (per-type stage B,
B1b): every `sregs` entry comes from a stream descriptor setting `ClientStreams` or `ServerStreams`
(`RegisterService`'s premise; `RegisterHealthServer`'s one stream, health's `Watch`, is
`ServerStreams`), since grpc runs an unflagged stream descriptor's handler directly, without the
stream interceptor (`server.go:1446-1450`, test T10b), which the `Serve` model does not represent. -/
def grpcSrvNew (gs : Loc) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(∃ (so : google_golang_org.grpc.serverOptions) (sh : GoInterface) (lis conns svm cv q d : Loc)
      (rs : List GrpcSrvReg) (ils : List Loc) (M : GMap GoString Loc),
    structFieldRef google_golang_org.grpc.Server go!"opts" gs ↦ so ∗ srvOptsIs so sh ics sics ∗
    structFieldRef google_golang_org.grpc.Server go!"statsHandler" gs ↦ sh ∗
    sync.isMutex (structFieldRef google_golang_org.grpc.Server go!"mu" gs) (BI.pure True : IProp GF) ∗
    structFieldRef google_golang_org.grpc.Server go!"lis" gs ↦ lis ∗
    ownMap lis (DFrac.own 1) (∅ : GMap GoInterface Bool) ∗
    structFieldRef google_golang_org.grpc.Server go!"conns" gs ↦ conns ∗
    ownMap conns (DFrac.own 1) (∅ : GMap GoString Loc) ∗
    structFieldRef google_golang_org.grpc.Server go!"serve" gs ↦ false ∗
    structFieldRef google_golang_org.grpc.Server go!"drain" gs ↦ false ∗
    structFieldRef google_golang_org.grpc.Server go!"cv" gs ↦ cv ∗
    sync.isCond cv (interface.mk (go.GoType.PointerType _root_.Perennial.sync.Mutex.ty)
      #(structFieldRef google_golang_org.grpc.Server go!"mu" gs)) ∗
    structFieldRef google_golang_org.grpc.Server go!"services" gs ↦ svm ∗
    ownMap svm (DFrac.own 1) M ∗
    structFieldRef google_golang_org.grpc.Server go!"events" gs ↦ GoInterface.nil ∗
    structFieldRef google_golang_org.grpc.Server go!"quit" gs ↦ q ∗
    srvEventIs q ∗
    structFieldRef google_golang_org.grpc.Server go!"done" gs ↦ d ∗
    srvEventIs d ∗
    structFieldRef google_golang_org.grpc.Server go!"serveWG" gs ↦ (zero_val _root_.Perennial.sync.WaitGroup) ∗
    structFieldRef google_golang_org.grpc.Server go!"handlersWG" gs ↦ (zero_val _root_.Perennial.sync.WaitGroup) ∗
    ⌜svcs = rs.map (·.sn) ∧ svcs.Nodup ∧ ils.length = rs.length ∧
      (∀ n, M !! n = map.lookupL n (svcs.zip ils)) ∧
      regs = rs.flatMap (fun r => descRegs r.sn r.mds r.ss) ∧
      sregs = rs.flatMap (fun r => descSRegs r.sn r.sds r.ss) ∧
      ∀ r ∈ rs, ∀ sd ∈ r.sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝ ∗
    [∗list] r; il ∈ rs; ils, srvRegIs gs r il)

/-- **Go's `maxAlloc` on linux/amd64** (`runtime/malloc.go:213,220`): grpc's codecs `make` a
reply's encoded length before any size check (protobuf-go `proto/encode.go:184-194`; grpc's default
codec `internal/mem/buffer_pool.go:354-356`, page-rounded), and `make` panics above this. A reply
at most this long marshals; in `(2 ^ 31 - 1, 2 ^ 48]` it then fails with `ResourceExhausted`
(etcd's `MaxSendMsgSize`, `encode`'s `MaxUint32` check), which the client's attempt contract
allows. Running out of memory below it is outside the model. -/
def grpcReplyMax : Nat := 2 ^ 48

/-- **The replies fit** (opaque; a named workload premise, D19a's first kind, as
`apply.backendUnderQuota` and `authRecordsFit`): in every run of the theorem's program, every reply
message a gRPC server marshals for sending (a unary reply after its handler returns, a stream
handler's `SendMsg`/`Send`) has an encoded length, as a natural number, of at most `grpcReplyMax`,
counting a submessage, or a byte slice's contents, once per reference (`notes/reply-size.md`).
Global, one for the run, not per server. It is about the replies to the calls of the program's own
clients: a process outside the program could connect to a member's port and send the request
below that makes it false, which every closed theorem's premise `addrsUnclaimed`
(`Proof/runtime/Start.lean`, part (a): no other process connects to an address of the program;
2026-11-14) excludes.

**What makes it true**: each byte slice and submessage is referenced a bounded number of times
per reply, so the encoding is at most a small multiple of the memory the reply references, and Go's
user address space on linux/amd64 is `2 ^ 47` bytes (out of memory comes first); or the workload's
replies are small outright.

**True of the closed theorems' programs**, whose replies are at most tens of kilobytes:
- putget, putget3, putgetc: one point `Get`;
- linkvtxn, and linkv3p's `Main` (linkvtxn's workload over three members, through bridges): point
  operations, flat transactions of at most three point operations, and one bounded range;
- authkv: fixed literals, its one nested transaction a write; root's watch of every key from
  revision 1, whose replies batch the run's few small writes (a watch reply at most 1000 revisions);
- k8setcd3: a bounded loop. k8s' keys-only `getKeys` runs only with the cacher's size estimation,
  which this program never builds;
- the watch examples (watchkv, cachekv, linkv3p's `MainWatch`): small literal prefixes; a watch
  reply batches at most 1000 revisions (`watchBatchMaxRevs`) of one small put each, tens of
  kilobytes. cachekv's `etcd/cache` library adds its own requests: a whole-prefix `Get`, a
  count-only `Get` with limit 1, a prefix watch with progress and created notifications, and
  `RequestProgress`, all over the same few small keys.
None of them sends a transaction of many keys-only ranges.

**False of** etcd under a client that sends a transaction whose nested transactions hold many
keys-only ranges over long keys (`issues/etcd-txn-keysonly-reply-alloc-panic.md`, reproduced: 4
keys under a 32 MiB `--max-request-bytes`, a 12.8 GiB member, the panic). A keys-only range's
`KeyValue`s share the index's key slices (`mvcc/index.go:181`, `kvstore_txn.go:88-106`), and
`checkTxnRequest` bounds the operations per nesting level, not the tree, so the reply's encoding
grows with the leaves times the keys' bytes and can pass `grpcReplyMax`, which panics the member
marshalling it. Such a transaction is not read-only (`IsTxnReadonly` looks at the top level only,
where its operations are transactions), so it goes through raft, bounded by `--max-request-bytes`,
and every member builds the reply in apply; the member serving the client marshals it. A flat
read-only transaction is served locally, without the proposal's `--max-request-bytes` check, but
holds at most `--max-txn-ops` ranges (128 by default), so its reply is at most that many copies of
the stored keys' keys-only encodings (each key's bytes plus at most 34 bytes of revisions and
framing): below `grpcReplyMax` unless that limit times the sum of those encodings passes it (at
the defaults, 2 TiB of such encodings; the suggested maximum quota is 8 GiB). Also false of a program whose handler
returns a reply sharing a submessage or byte slice many times. A theorem taking this premise says
nothing about such runs. The client's send side has its own checked premise (`grpcInvokerOk`'s
`Req.wireLen m < grpcMsgMax`). -/
opaque grpcRepliesFit : Prop

end defs

end EtcdGrove
end Perennial
