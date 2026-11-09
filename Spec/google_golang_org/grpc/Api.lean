/-
# grpc-go: the trust boundary (batch 2a)

grpc-go (v1.84.0 at the pin) is not translated (`Code/google_golang_org/grpc*.toml`: names and
types only): every spec of `Spec/google_golang_org/grpc/**` is **assumed**, true of grpc-go's code
at the pin (each file says why). They are stated over this one vocabulary. What the old boundary
got wrong, and this one avoids (`specs-ref/notes/grpc-msg-models.md`, `per-type-blockers.md`,
`pbenc-ok-inconsistent.md`, `reply-size.md`, `invoke-size.md`):

* **No caller-built message model**: a message is `Proto.msgAt t p dq c`, its content `c` a value
  (`Proto/Api.lean`), and grpc transports contents' wire views: the server's decoded request holds
  `norm c` of the content `c` the client's message held, the client's decoded reply `norm` of the
  handler's reply's (verify-round, A6 F2: a non-`nil` empty `bytes` field arrives `nil`), and every
  decoded message is canonical (`⌜norm c = c⌝`, in place of the old `Proto.decodedAt`). What
  a content means is the message type's owner's law, which nobody can choose per call.
* **Handler runs borrow their caller's thread tokens** (round 1, as 2f's net/http: the
  repository's handler-pool decision): `start` takes a pool of `n` of the caller's thread tokens
  (2f's `Http.handlerPool`); each run draws one for its life and returns it. The physical premise:
  grpc runs at most `n` handlers of one server at once, a bound the adequacy theorem fixes. On the
  TLS path the runs are net/http's (`ServeHTTP`), with net/http's pool. No statement here hands out
  a token it did not take.
* **One address, one protocol** (round 1): an address is bound through 2f's `Http.protoAt` to the
  protocol `grpcOver C P` (`addrAt`), with net/http's listeners (`Http.listenerAt`, 2f's
  `net.Listen`) and environment premise (one reserved string per socket). cmux's sub-listeners
  (`cmuxSubAt`) and the TLS path (`Server.ServeHTTP`) serve that same protocol.
* **Status messages** arrive as `fixUtf8 msg` (invalid UTF-8 replaced); etcd's are ASCII.
* **Sizes**: grpc-go's codec allocates `proto.Size` bytes before any size check, and `make` panics
  above `2 ^ 48` (`issues/grpc-codec-alloc-before-size-check.md`); a reply or request over the
  limits below that is refused with `ResourceExhausted`, which is no panic. So the boundary holds
  only for programs whose gRPC messages fit (`Proto.Content.fits`). That is **a workload premise,
  `msgsFit`**, taken where a connection or a server is made (`NewClient.spec`, `Server.Serve.spec`),
  carried by the handles, never by a call (PRINCIPLES, "A workload premise about a resource's later
  operations goes on the resource's only producer"; the old `grpcRepliesFit`, approved
  2026-10-31). It is a scope restriction: W0 asked that sending an oversized message return an
  error rather than panic; that is **false of grpc-go** for an encoding over `2 ^ 48` bytes (a
  message sharing one submessage or byte slice many times: a `Txn` holding one `Op` `2 ^ 18` times
  over a 1 GiB value), and true below it.

## What a call does (the contracts)

* A **unary method** is registered with a contract `S : UnarySpec` (`MD → Content → (Outcome →
  IProp) → IProp`): the caller hands over `S md (norm c) Φ` with its request of content `c` (the
  server sees the metadata `md` and decodes `norm c`), and gets `Φ o` back with the outcome `o` the handler produced: a reply's
  content, or a status (code, message). This is Grove's urpc shape (the caller's resource travels
  with the call). **At most one run per attempt**: grpc-go resends an attempt by itself only when
  the stream never reached the server's handler (transparent retry of an unprocessed stream; no
  service-config retry policy: `dialOptAt`'s options cannot set one), so `S md c Φ` is consumed by
  at most one run.
* An **error grpc made itself** (`ownErr`: the context's, a transport's, a limit's, an
  unmarshaling failure's) carries one of grpc's own messages (`grpcMsg`), never a handler's: the
  client learns nothing from it, and the contract it handed over is lost (the run may still
  happen). grpc-go v1.84 has **no** error with the messages etcd's client tests for an attempt never
  sent ("there is no address available", "there is no connection available", `retry.go:93`):
  W0's `CallErr.notSent` is never produced.
* A **streaming method** is registered with a `StreamSpec` (`up`, `dn`, `fin`): the client's
  `i`-th message carries `up g md i c`, the server's `j`-th `dn g md j c`, the end (`io.EOF` for a
  handler that returned `nil`, else its status) `fin g md n o` with `n` the number of messages the
  client received, which is all the server sent; `g` names the stream (the same at both ends:
  ghost state a protocol keys by it). Messages go intact, in order, once.

## Vocabulary

Pure: the codes (`cOK`, ...), `MD` (metadata as the server sees it: lowercase keys, values),
`MD.get`, `Outcome`, `UnarySpec`, `StreamSpec`, `StreamName` (opaque), `grpcMsg` (opaque: grpc's
own messages), `msgsFit` (opaque `Prop`: the workload premise).

Resources (persistent unless said):
* `statusErr err code msg`: `err` is a gRPC status error with that code and message (what
  `status.FromError` reads). `sentStatus err code msg`: what a server sends for a handler's
  returned error `err` (its status; `Unknown` and `err.Error()` for a non-status error; the
  context's code for a context's error). `ownErr err`.
* `outMD ctx md`: the outgoing metadata of the client-side context `ctx` (`metadata`'s specs).
* `connAt cc A ui si R`: the `*grpc.ClientConn` `cc`, dialed with unary and stream interceptors
  `ui`, `si` (`none`: grpc's invoker/streamer directly), reaching only addresses `ep` with `A ep`
  (its resolver's), its per-RPC credentials adding metadata `mdc` with `□ R mdc`.
* `dialOptAt v f`: the `grpc.DialOption` value `v` acts on a dial's configuration as `f`
  (`DialCfg`).
* `callOptOk v`: a `grpc.CallOption` grpc's call accepts (wait-for-ready, message-size limits,
  `Peer`, ...).
* `serves ep m reqT repT S`, `servesStream ep m reqT repT S`: the method `m` (`"/svc/Method"`) is
  served at `ep` with the contract `S`, its request and reply of the Go types `*reqT`, `*repT`.
* `attemptOk cc A inv`: grpc's one-attempt invoker `inv` of `cc` (`attemptOk_call`).
* `streamerOk cc A str`: grpc's streamer (`streamerOk_call`).
* `rpcCtx ctx md`: the context a handler runs with: a `Context.ctxOk` context carrying the
  incoming metadata `md`, done when the client goes away or the stream ends.
* `decOk dec reqT c`: the request decoder a unary handler gets (`decOk_call`).
* `cliSend cs g S md i`, `cliRecv cs g S md n` (exclusive): a client stream's halves (`i`
  messages sent, `n` received); `srvRecv st g S md i`, `srvSend st g S md j` (exclusive): a server
  stream's.
* `srvBuild gs B` (exclusive): a `*grpc.Server` being built (`SrvCfg`: its interceptors and
  registrations so far); `srvOptAt v f`: a `grpc.ServerOption` acting as `f`.
* `unaryOk h ss ic reqT repT S`, `streamOk h ss sic reqT repT S`: a registered handler meets its
  contract (what `Serve` takes, what the registering package proves).

## Laws

`grpc_persistent`, `ownErr_grpcMsg`, `statusErr_sent` (with `ownErr_grpcMsg`: an own error is sent
as itself), `statusErr_agree`, `icChain_nil`, `cliIcPass_call`,
`decOk_call`, `attemptOk_call`, `streamerOk_call`, the stream halves' `cliSend_send`,
`cliSend_closeSend`, `cliRecv_recv`, `srvRecv_recv`, `srvSend_send`, `srvStream_context`.
-/
module

public import Spec.google_golang_org.protobuf.proto.Api
public import Spec.context.Api
public import Spec.net.http.Api
public import Perennial.Code.io
public import GeneratedProof.google_golang_org.grpc
public import GeneratedProof.google_golang_org.grpc.status
public import GeneratedProof.google_golang_org.grpc.metadata
public import GeneratedProof.google_golang_org.grpc.peer
public import Spec.PkgInit.google_golang_org.grpc
public import Spec.PkgInit.google_golang_org.grpc.status
public import Spec.PkgInit.google_golang_org.grpc.metadata

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI Proto

/-! ## Codes (`google.golang.org/grpc/codes`) -/

def cOK : w32 := W32 0
def cCanceled : w32 := W32 1
def cUnknown : w32 := W32 2
def cInvalidArgument : w32 := W32 3
def cDeadlineExceeded : w32 := W32 4
def cNotFound : w32 := W32 5
def cAlreadyExists : w32 := W32 6
def cPermissionDenied : w32 := W32 7
def cResourceExhausted : w32 := W32 8
def cFailedPrecondition : w32 := W32 9
def cAborted : w32 := W32 10
def cOutOfRange : w32 := W32 11
def cUnimplemented : w32 := W32 12
def cInternal : w32 := W32 13
def cUnavailable : w32 := W32 14
def cDataLoss : w32 := W32 15
def cUnauthenticated : w32 := W32 16

/-! ## Metadata, outcomes, contracts -/

/-- **Metadata** as a list of (key, values), keys lowercase (grpc lowercases them on the wire). -/
abbrev MD := List (GoString × List GoString)

/-- The values of key `k`, in order. -/
def MD.get (md : MD) (k : GoString) : List GoString :=
  (md.filter (fun e => decide (e.1 = k))).flatMap (·.2)

/-- The keys grpc adds or reserves on the server side (`:authority`, `content-type`,
`user-agent`, `grpc-*`): opaque, none of them a key etcd uses. -/
opaque reservedKey : GoString → Prop

/-- **What the server sees of the client's metadata `md0`**: the same values for every key grpc
does not reserve. -/
def mdSeen (md0 md : MD) : Prop := ∀ k, ¬ reservedKey k → md.get k = md0.get k

/-- ASCII lowercase (grpc's `strings.ToLower` of metadata keys, which are ASCII). -/
def lowerKey (k : GoString) : GoString :=
  k.map (fun b => if W8 65 ≤ b ∧ b ≤ W8 90 then b + W8 32 else b)

/-- `md.Set(k, vs...)`: the key's values replaced. -/
def MD.set (md : MD) (k : GoString) (vs : List GoString) : MD :=
  (md.filter (fun e => decide (e.1 ≠ lowerKey k))) ++ [(lowerKey k, vs)]

/-- `Pairs(kv...)` / `AppendToOutgoingContext`'s pairs: keys lowercased, in order. -/
def MD.ofPairs : List GoString → MD
  | k :: v :: rest => (lowerKey k, [v]) :: MD.ofPairs rest
  | _ => []

/-- **The outcome of a run**: the reply's content, or a status. -/
inductive Outcome where
  | ok (c : Content)
  | status (code : w32) (msg : GoString)

/-- **The messages of grpc's own errors** (opaque): the messages grpc-go's code makes. -/
opaque grpcMsg : GoString → Prop

/-- **A status message as it arrives** (opaque): grpc-go's server percent-encodes `grpc-message`,
replacing each invalid UTF-8 sequence by U+FFFD (`internal/transport/http_util.go`,
`encodeGrpcMessageUnchecked`); an ASCII message arrives as itself (`fixUtf8_ascii`). -/
opaque fixUtf8 : GoString → GoString

/-- An ASCII message arrives unchanged. -/
def fixUtf8_ascii.spec : Prop := ∀ m : GoString, (∀ b ∈ m, uint.nat b < 128) → fixUtf8 m = m

/-- A message that arrives as an ASCII string was that string (U+FFFD is not ASCII). -/
def fixUtf8_ascii_inv.spec : Prop := ∀ m m' : GoString, (∀ b ∈ m', uint.nat b < 128) →
  fixUtf8 m = m' → m = m'

/-- **The text of a status error** (`(*status.Error).Error()`: `"rpc error: code = ... desc =
..."`), opaque, never empty. -/
opaque grpcText : w32 → GoString → GoString

def grpcText_ne.spec : Prop := ∀ c m, grpcText c m ≠ []

/-- **An HTTP request that grpc's `ServeHTTP` takes as a gRPC call** (opaque): HTTP/2 `POST` with a
`Content-Type` beginning with `application/grpc` (2f's `HReq`). -/
opaque grpcReq : Http.HReq → Prop

/-- **The workload premise** (see the header): every message this program's gRPC clients and
servers marshal fits (`Proto.Content.fits`). Opaque: a scope restriction of the results that take
it, which say so. -/
opaque msgsFit : Prop

/-- Ghost names of one stream: opaque. -/
opaque StreamName : Type := Unit

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A unary method's contract**: what a caller hands over with a request of content `c` sent with
metadata `md`, to get `Φ o` back for the outcome `o`. -/
abbrev UnarySpec := MD → Content → (Outcome → IProp GF) → IProp GF

/-- **A streaming method's contract** (see the header). -/
structure StreamSpec where
  up : StreamName → MD → Nat → Content → IProp GF
  dn : StreamName → MD → Nat → Content → IProp GF
  fin : StreamName → MD → Nat → Option (w32 × GoString) → IProp GF

/-- A dial's configuration, as far as the specs model it: the interceptors, the addresses the
resolver may report (`A`), what the per-RPC credentials add (`R`), and whether a retry policy is
configured (never, for an option of `dialOptAt`). -/
structure DialCfg where
  ui : Option val
  si : Option val
  A : GoString → IProp GF
  R : MD → IProp GF

/-- A server being built: its chained interceptors and its registrations (method name, handler of
the `MethodDesc`/`StreamDesc`, service value). -/
structure SrvCfg where
  ics : List GoFunc
  sics : List GoFunc
  regs : List (GoString × val × GoInterface)
  sregs : List (GoString × val × GoInterface)

/-- **`err` is a gRPC status error** with `code` and `msg`. -/
opaque statusErr [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) (code : w32) (msg : GoString) : IProp GF := iprop(True)

/-- **`err`'s `Error()` returns `msg`**, on every call (persistent; `err` not nil): what
`status.FromError` reads of an error that is not a status. -/
opaque errMsg [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) (msg : GoString) : IProp GF := iprop(True)

/-- **`err` carries no gRPC status** (persistent): neither it nor an error it wraps (`errors.As`)
has a `GRPCStatus()` method; what `status.FromError` needs to build `Unknown` from `Error()`. -/
opaque plainErr [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) : IProp GF := iprop(True)

/-- **The dynamic type of `err` is comparable** (`==` and a map lookup keyed by it never panic:
Perennial's `CheckComparable`). -/
opaque cmpErr (err : GoInterface) : Prop

/-- **A `*status.Status` with `code` and `msg`** (persistent; read-only: grpc never writes one it
handed out; `nil` is `OK` with no message). -/
opaque statusAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (code : w32) (msg : GoString) : IProp GF := iprop(True)

/-- **What `status.FromError` sees of `err`**: a status error (`ok`), or another error, `Unknown`
with its message (not `ok`), or `nil` (`OK`, `ok`). -/
def errView (err : GoInterface) (code : w32) (msg : GoString) (ok : Bool) : IProp GF :=
  iprop((⌜ok = true⌝ ∗ statusErr err code msg) ∨
        (⌜ok = false ∧ code = cUnknown⌝ ∗ errMsg err msg ∗ plainErr err) ∨
        ⌜err = GoInterface.nil ∧ ok = true ∧ code = cOK ∧ msg = []⌝)

/-- **A `*peer.Peer` grpc made** (persistent; `peer.FromContext`'s): read-only, its fields print,
its remote address set (`peer/Api.lean`'s `peerOk_fields`: verify round, A6 completeness F3). -/
opaque peerOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) : IProp GF := iprop(True)

/-- **The status a server sends for a handler's error `err`**. -/
opaque sentStatus [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) (code : w32) (msg : GoString) : IProp GF := iprop(True)

/-- **An error grpc made itself** (see the header). -/
opaque ownErr [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) : IProp GF := iprop(True)

/-- **The outgoing metadata of `ctx` is `md`**. -/
opaque outMD [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (md : MD) : IProp GF := iprop(True)

/-- **A `metadata.MD` map at `m` holding `md`** (fraction `dq` of the map; its value slices
read-only). Intended realization: Perennial's `ownMap m dq` of the keys to slices, each slice
`↦*□` its strings (`mdAt_index`, a law of the realization, gives the map lookup `md[k]` the
server's interceptors make). -/
opaque mdAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (dq : DFrac) (md : MD) : IProp GF := iprop(True)

/-- **A metadata map that may be `nil`** (re-review R-A6 N1): `nil` (reads as empty: Go allows
`Get`, `Copy`, `len` and lookups on a `nil` map) when `isNil`, else `mdAt`. `mdAt` itself is never
of `nil` (its realization is an `ownMap`, a heap points-to: `heapPointsto_non_null`); the `nil` case
lives outside it, as `FromIncomingContext` does. -/
def mdAtN (isNil : Bool) (m : Loc) (dq : DFrac) (md : MD) : IProp GF :=
  if isNil then iprop(⌜m = null ∧ md = []⌝) else mdAt m dq md

/-- **A client connection** (see the header). -/
opaque connAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cc : Loc) (A : GoString → IProp GF) (ui si : Option val) (R : MD → IProp GF) :
  IProp GF := iprop(True)

/-- **A dial option acting as `f`**. -/
opaque dialOptAt (v : GoInterface) (f : DialCfg (GF := GF) → DialCfg (GF := GF)) : IProp GF :=
  iprop(True)

/-- **A client unary interceptor that passes the call through** (persistent; verify-round,
A6-completeness F2 / A2-completeness F2: Kubernetes' `grpc.WithChainUnaryInterceptor`, grpc-
prometheus's): it calls its invoker exactly once with its own arguments and returns its result
(`cliIcPass_call`), observing only. -/
opaque cliIcPass [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (i : val) : IProp GF := iprop(True)

/-- **A client stream interceptor that passes the stream through** (persistent; the same for
`WithChainStreamInterceptor`): it calls its streamer exactly once with its own arguments and returns
the stream (possibly wrapped by a value whose `SendMsg`, `RecvMsg`, `CloseSend`, `Context`,
`Header`, `Trailer` call the wrapped stream's once with the same arguments and return their
results) or the streamer's error. Its meaning is this docstring: whoever offers such an interceptor
(grpc-prometheus's, assumed by its user) states it. -/
opaque cliSicPass [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (i : val) : IProp GF := iprop(True)

/-- **A `stats.Handler` that only observes** (persistent): its `TagRPC`, `HandleRPC`, `TagConn`,
`HandleConn` return (no panic) from any goroutine, `TagRPC`/`TagConn` returning a context derived
from theirs by values (otelgrpc's span), writing nothing the program's specs own. -/
opaque statsOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (h : GoInterface) : IProp GF := iprop(True)

/-- **A context dialer that dials the address it is given** (persistent; `WithContextDialer`'s
argument, Kubernetes' egress dialer): `f(ctx, addr)` returns a `net.Conn` to `addr`, or an error;
it never connects elsewhere (the addresses reached stay the resolver's: `DialCfg.A`). -/
opaque ctxDialerOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (f : val) : IProp GF := iprop(True)

/-- **A call option grpc accepts**. -/
opaque callOptOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (v : GoInterface) : IProp GF := iprop(True)

/-- **The contracts an address is bound to**: for each method name, its request and reply types
and its contract (`none`: not served there). -/
structure AddrContract where
  unary : GoString → Option (go.GoType × go.GoType × UnarySpec (GF := GF))
  stream : GoString → Option (go.GoType × go.GoType × StreamSpec (GF := GF))

/-- **The HTTP protocol of a gRPC server meeting `C`, other requests by `P`** (opaque; 2f's
`Http.Proto`): a request that is a gRPC call (`grpcReq`) is answered as `C` says for its method;
any other request as `P` says (etcd's gateway, `/health`, `/metrics` on the same socket). One
address, one protocol: a socket bound for etcd's gRPC contracts cannot be served by net/http with
another protocol; etcd's TLS path (net/http serving `grpcHandlerFunc`, which hands gRPC calls to
`ServeHTTP`) meets this protocol through `Server.ServeHTTP.spec`. -/
opaque grpcOver (_C : AddrContract (GF := GF)) (P : Http.Proto GF) : Http.Proto GF := P

/-- **The address `ep` is bound to the contracts `C`** for good (persistent): 2f's `protoAt` of the
address string, set once from the environment's `Http.addrFree ep` (`Http.reserve`; the
environment's premise: one reserved string per socket), so every server the program ever starts
at `ep` serves `C` (a member restarted at its client URL serves the same contracts). -/
def addrAt (ep : GoString) (C : AddrContract (GF := GF)) : IProp GF :=
  iprop(∃ P : Http.Proto GF, Http.protoAt ep (grpcOver C P))

/-- **The unary method `m` is served at `ep`** with the contract `S`. -/
def serves (ep m : GoString) (reqT repT : go.GoType) (S : UnarySpec (GF := GF)) : IProp GF :=
  iprop(∃ C : AddrContract (GF := GF), addrAt ep C ∗ ⌜C.unary m = some (reqT, repT, S)⌝)

/-- **The streaming method `m` is served at `ep`** with the contract `S`. -/
def servesStream (ep m : GoString) (reqT repT : go.GoType) (S : StreamSpec (GF := GF)) : IProp GF :=
  iprop(∃ C : AddrContract (GF := GF), addrAt ep C ∗ ⌜C.stream m = some (reqT, repT, S)⌝)

/-- **A cmux sub-listener** (exclusive): the connections of a listener bound at `ep` (2f's
`Http.listenerAt`) that cmux matched as HTTP/2 (`http2`) or HTTP/1 (etcd's insecure client path,
`embed/serve.go:141-213`). cmux (`github.com/soheilhy/cmux`) is not translated: its functions'
specs (`New`, `Match`, `HTTP1`, `HTTP2`, `Serve`) wait for its names in the Goose configuration
(asked of 2e); `cmux_split` is what they give. -/
opaque cmuxSubAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (lis : GoInterface) (ep : GoString) (http2 : Bool) : IProp GF := iprop(True)

/-- **A listener a gRPC server may serve at `ep`**: one `net.Listen` bound (2f's `Listen.spec`), or
cmux's HTTP/2 part of one. -/
def grpcListener (lis : GoInterface) (ep : GoString) : IProp GF :=
  iprop(Http.listenerAt lis ep ∨ cmuxSubAt lis ep true)

/-- **A started gRPC server serving `C` through `ServeHTTP`** (persistent; `startHTTP`'s). -/
opaque servesHTTP (gs : Loc) (C : AddrContract (GF := GF)) : IProp GF := iprop(True)

/-- **The context of a server stream** (persistent; the run's, given with the halves): what
`Context()` returns to any goroutine. -/
opaque srvCtxOf [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (st : GoInterface) (ctx : GoInterface) (md : MD) : IProp GF := iprop(True)

/-- **A client stream's context** (persistent): what `cs.Context()` returns. -/
opaque cliCtxOf [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cs : GoInterface) (ctx : GoInterface) : IProp GF := iprop(True)

/-- **grpc's generic stream wrappers** (`*GenericClientStream[Req, Res]`, `*GenericServerStream[Req,
Res]`, which the generated stubs and handlers make, 3h): `w`'s embedded stream is `s`. -/
opaque genCliAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) (cs : GoInterface) (reqT repT : go.GoType) : IProp GF := iprop(True)
opaque genSrvAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) (st : GoInterface) (reqT repT : go.GoType) : IProp GF := iprop(True)

/-- grpc's health service's registrations (`grpc_health_v1.Health_ServiceDesc`'s unary `Check`,
`List` and stream `Watch`, full names with handlers; opaque). -/
opaque healthMethods : List (GoString × val)
opaque healthStreams : List (GoString × val)

/-- **A `peer.Peer` struct variable at `p`, lent to grpc** (persistent; `grpc.Peer(&p)`'s: grpc
copies the attempt's peer into it, `*o.PeerAddr = *x`, after each attempt): an invariant holds its
fields, each one that prints (`peer/Api.lean`'s `peerVar_inv`; verify round, A6 completeness F3: was
a `*peer.Peer` variable, while the caller's `var p peer.Peer` is a struct). -/
opaque peerVar [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) : IProp GF := iprop(True)

/-- **The right to run `Serve` on `gs` with `lis`** (exclusive; `start`'s). -/
opaque serveTok [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (gs : Loc) (lis : GoInterface) : IProp GF := iprop(True)

/-- **The run resources `start` lent** (exclusive; integration X): `n` copies of `T`, given back by
`GracefulStop` once the runs have returned, with the pool's `n` thread tokens (verify-round). -/
opaque drainTok [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (gs : Loc) (T : IProp GF) (n : Nat) : IProp GF := iprop(True)

/-- **A `*grpc.ServiceDesc`** (read-only; the generated `<Svc>_ServiceDesc`, 3h's init facts): the
service's full name, its unary methods' (name, `Handler`) and its streams' (name, `Handler`). -/
opaque serviceDescAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (sd : Loc) (svc : GoString) (ms ss : List (GoString × val)) : IProp GF :=
  iprop(True)

/-- **grpc's `*health.Server`** (persistent: its methods lock internally). -/
opaque healthAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (hs : Loc) : IProp GF := iprop(True)

/-- **A resolver builder reporting only addresses with `A`** (persistent; the client's resolver,
1c, over grpc's `resolver/manual`). -/
opaque resolverAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : GoInterface) (A : GoString → IProp GF) : IProp GF := iprop(True)

/-- **Per-RPC credentials adding metadata with `R`** (persistent; the client's token bundle's,
1c: grpc calls its `GetRequestMetadata` on every call and stream, and its
`RequireTransportSecurity`). -/
opaque perRPCAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (pc : GoInterface) (R : MD → IProp GF) : IProp GF := iprop(True)

/-- **A codec that round-trips contents** (persistent; `grpc.CustomCodec`'s argument: its
`Marshal` of a message holding `c` gives bytes `encodes`-ing `c`, its `Unmarshal` of such bytes into
a fresh message gives `c`; v3rpc's `codec`, over golang/protobuf's `proto`, which calls
protobuf-go's). -/
opaque codecOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cd : GoInterface) : IProp GF := iprop(True)

/-- **The chained unary interceptor of `ics`** (persistent): what grpc passes to a handler. -/
opaque icChain [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ics : List GoFunc) (ic : val) : IProp GF := iprop(True)

/-- **A unary server handler continuation** (what an interceptor gets as `handler`): calling it is
running the rest of the chain `ics` and then `h` (the generated handler's call of the service's
method). -/
opaque icHandler [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ics : List GoFunc) (info : Loc) (k : val) (h : val) : IProp GF := iprop(True)

/-- **grpc's one-attempt invoker of `cc`** (the `UnaryInvoker` an interceptor gets). -/
opaque attemptOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cc : Loc) (A : GoString → IProp GF) (R : MD → IProp GF) (inv : val) : IProp GF :=
  iprop(True)

/-- **grpc's streamer of `cc`** (the `Streamer` a stream interceptor gets). -/
opaque streamerOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cc : Loc) (A : GoString → IProp GF) (R : MD → IProp GF) (str : val) : IProp GF :=
  iprop(True)

/-- **The context of a handler run**, with the incoming metadata `md`. -/
opaque rpcCtx [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (md : MD) : IProp GF := iprop(True)

/-! #### Any context's incoming metadata and TLS peer (integration I3)

What `metadata.FromIncomingContext` and `peer.FromContext` read of **any** context, not only a
run's: the auth store's `AuthInfoFromCtx`/`AuthInfoFromTLS`/`WithRoot` (3d) and the server's
internal requesters (2c's `ctxNoIncoming`) read them. These realize 3d's provisional
`Auth.ctxInMD`, `Auth.ctxPeerCN`, `Auth.ctxCertUser` (`req/google_golang_org_grpc.md`, "from 3d"):
the owner of `server/v3/auth/Api.lean` should define them as these. -/

/-- **`ctx`'s incoming metadata is `o`** (persistent): `metadata.FromIncomingContext`'s answer,
`none` for a context carrying none (`Background()`-derived, the server's `s.ctx`). A run's context
has `some md` (`rpcCtx_inMD`). -/
opaque ctxInMD [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (o : Option MD) : IProp GF := iprop(True)

/-- **`ctx`'s TLS peer identity** (persistent): `some cn` for a context whose `peer.FromContext`
peer is a TLS peer (`credentials.TLSInfo`) with a non-empty verified chain whose first chain's leaf
has common name `cn`; `none` otherwise (no peer, not TLS, no verified chain). -/
opaque ctxPeerCN [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (c : Option GoString) : IProp GF := iprop(True)

/-- **The identity `AuthInfoFromTLS` reads** (transparent): the peer's common name when the
incoming metadata is present and has no `grpcgateway-accept` key; `none` otherwise. -/
def ctxCertUser (ctx : GoInterface) (c : Option GoString) : IProp GF :=
  iprop(∃ (o : Option MD) (pc : Option GoString), ctxInMD ctx o ∗ ctxPeerCN ctx pc ∗
    ⌜c = match o with
      | some md => if md.get (go!"grpcgateway-accept") = [] then pc else none
      | none => none⌝)

/-- **The request decoder of a unary run** (the request's content `c`). -/
opaque decOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (dec : val) (reqT : go.GoType) (c : Content) : IProp GF := iprop(True)

/-- **The key of the stream `g`** (exclusive; given to the client that opened it, once): what a
stream's protocol consumes to allocate ghost state keyed by `g` (so that the client's first message
can fix the parameters the server's later messages are about). Allocating ghost names is free: this
is no counted resource. -/
opaque streamKey [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (g : StreamName) : IProp GF := iprop(True)

/-- A client stream's sending half (`i` sent). -/
opaque cliSend (cs : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF)) (md : MD) (i : Nat) :
  IProp GF := iprop(True)
/-- A client stream's receiving half (`n` received). -/
opaque cliRecv (cs : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF)) (md : MD) (n : Nat) :
  IProp GF := iprop(True)
/-- A server stream's receiving half (`i` received). -/
opaque srvRecv (st : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF)) (md : MD) (i : Nat) :
  IProp GF := iprop(True)
/-- A server stream's sending half (`j` sent). -/
opaque srvSend (st : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF)) (md : MD) (j : Nat) :
  IProp GF := iprop(True)

/-- **A server being built**. -/
opaque srvBuild [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (gs : Loc) (B : SrvCfg) : IProp GF := iprop(True)

/-- **A server option acting as `f`** on the interceptors (the codec, credentials, limits and
stats handlers change nothing the specs model). -/
opaque srvOptAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (v : GoInterface) (f : SrvCfg → SrvCfg) : IProp GF := iprop(True)

/-- What a unary handler returns for its caller's `Φ`: a reply message (any fraction: grpc only
reads it; nested less than protobuf's decoding limit, so the caller can decode it) with `Φ` of its
content's wire view (what the caller decodes), or an error with `Φ` of the status sent, or an error grpc made
itself (the dropped decoding of a request, which `decOk` excludes; a codec's). -/
def unaryOut (repT : go.GoType) (r err : GoInterface) (Φ : Outcome → IProp GF) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ (p : Loc) (dq : DFrac) (c : Content),
          ⌜r = msgVal repT p ∧ depth c < depthMax⌝ ∗ msgAt repT p dq c ∗ Φ (.ok (norm c))) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ ∃ code msg, sentStatus err code msg ∗ Φ (.status code (fixUtf8 msg))))

/-- **The handler `h` of a unary method** (its `MethodDesc.Handler`, called by grpc with the
service value `ss`, the run's context, the decoder and the chained interceptor `ic`) **meets the
contract `S`**: a run with the thread's token and the server's run resource `T` (integration X: what
`start` lends each run, given back by `GracefulStop`) returns both and `unaryOut`. -/
def unaryOk (h : val) (ss : GoInterface) (ic : val) (reqT repT : go.GoType)
    (S : UnarySpec (GF := GF)) (T : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (md : MD) (dec : val) (c : Content) (Φ : Outcome → IProp GF),
    ∀ Ψ : val → IProp GF,
    threadTok ∗ T ∗ rpcCtx ctx md ∗ decOk dec reqT c ∗ S md c Φ ∗
      (∀ (r : GoInterface) (err : GoInterface), threadTok -∗ T -∗ unaryOut repT r err Φ -∗ Ψ (PairV #r #err)) -∗
    WP (App (App (App (App (Val h) (Val #ss)) (Val #ctx)) (Val dec)) (Val ic)) {{ Ψ }})

/-- What a stream handler returns: the end's facts for the messages it sent, given with the send
half (the count known), or for any count (a protocol whose end does not depend on it). -/
def streamOut (st : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF)) (md : MD)
    (err : GoInterface) : IProp GF :=
  iprop(∃ e : Option (w32 × GoString),
    ((⌜err = GoInterface.nil ∧ e = none⌝) ∨
     (⌜err ≠ GoInterface.nil⌝ ∗ ∃ code msg, sentStatus err code msg ∗ ⌜e = some (code, fixUtf8 msg)⌝)) ∗
    ((∃ j, srvSend st g S md j ∗ S.fin g md j e) ∨ □ ∀ j, S.fin g md j e))

/-- The call grpc makes for a stream run: the chained stream interceptor `sic` (with the
`*StreamServerInfo` `info` grpc allocates) around the handler, or the handler itself. -/
def streamRun (h : val) (ss st : GoInterface) (sic : Option val) (info : Loc) : Expr :=
  match sic with
  | none => App (App (Val h) (Val #ss)) (Val #st)
  | some i => App (App (App (App (Val i) (Val #ss)) (Val #st)) (Val #info)) (Val h)

/-- **The handler `h` of a streaming method** (its `StreamDesc.Handler`, called with the service
value and the run's server stream, under the chained stream interceptor `sic`) **meets `S`**: a run
with both halves of a fresh stream (and the run resource `T`, as `unaryOk`) returns `streamOut`. -/
def streamOk (h : val) (ss : GoInterface) (sic : Option val) (reqT repT : go.GoType)
    (S : StreamSpec (GF := GF)) (T : IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx st : GoInterface) (info : Loc) (md : MD) (g : StreamName) (Ψ : val → IProp GF),
    threadTok ∗ T ∗ rpcCtx ctx md ∗ srvCtxOf st ctx md ∗ srvRecv st g S md 0 ∗ srvSend st g S md 0 ∗
      (∀ (err : GoInterface), threadTok -∗ T -∗ streamOut st g S md err -∗ Ψ #err) -∗
    WP (streamRun h ss st sic info) {{ Ψ }})

/-! ### Laws -/

/-- **A pass-through unary interceptor's call** (WP form): calling it is calling its invoker with
the same arguments. -/
def cliIcPass_call.spec : Prop := ∀ (i : val) (ctx : GoInterface) (method : GoString)
    (req reply : GoInterface) (cc : Loc) (inv : val) (opts : GoSlice) (Ψ : val → IProp GF),
  cliIcPass (GF := GF) i ∗
    WP (App (App (App (App (App (App (Val inv) (Val #ctx)) (Val #method)) (Val #req)) (Val #reply))
      (Val #cc)) (Val #opts)) {{ Ψ }} ⊢
  WP (App (App (App (App (App (App (App (Val i) (Val #ctx)) (Val #method)) (Val #req)) (Val #reply))
      (Val #cc)) (Val inv)) (Val #opts)) {{ Ψ }}

def dialAux_persistent.spec : Prop :=
  (∀ i, Persistent (cliIcPass (GF := GF) i)) ∧ (∀ i, Persistent (cliSicPass (GF := GF) i)) ∧
  (∀ h, Persistent (statsOk (GF := GF) h)) ∧ (∀ f, Persistent (ctxDialerOk (GF := GF) f))

/-- `errMsg`'s meaning: `Error()` returns `msg`. -/
def errMsg_call.spec : Prop := ∀ (err : GoInterface) (msg : GoString),
  {{ errMsg (GF := GF) err msg }}
    (App (Val (err @!! go.error @!! go!"Error")) (Val #()))
  {{ RET #msg; True }}

/-- A non-status error is sent as `Unknown` with its message. -/
def errMsg_sent.spec : Prop := ∀ (err : GoInterface) (msg : GoString),
  errMsg (GF := GF) err msg ∗ (∀ c m, statusErr err c m -∗ False) ⊢ sentStatus err cUnknown msg

def grpc_persistent.spec : Prop :=
  (∀ err code msg, Persistent (statusErr (GF := GF) err code msg)) ∧
  (∀ err code msg, Persistent (sentStatus (GF := GF) err code msg)) ∧
  (∀ err, Persistent (ownErr (GF := GF) err)) ∧
  (∀ ctx md, Persistent (outMD (GF := GF) ctx md)) ∧
  (∀ cc A ui si R, Persistent (connAt (GF := GF) cc A ui si R)) ∧
  (∀ v f, Persistent (dialOptAt (GF := GF) v f)) ∧
  (∀ v, Persistent (callOptOk (GF := GF) v)) ∧
  (∀ ep m t t' S, Persistent (serves (GF := GF) ep m t t' S)) ∧
  (∀ ep m t t' S, Persistent (servesStream (GF := GF) ep m t t' S)) ∧
  (∀ cc A R inv, Persistent (attemptOk (GF := GF) cc A R inv)) ∧
  (∀ cc A R str, Persistent (streamerOk (GF := GF) cc A R str)) ∧
  (∀ ctx md, Persistent (rpcCtx (GF := GF) ctx md)) ∧
  (∀ v f, Persistent (srvOptAt (GF := GF) v f)) ∧
  (∀ err msg, Persistent (errMsg (GF := GF) err msg)) ∧
  (∀ s c m, Persistent (statusAt (GF := GF) s c m)) ∧
  (∀ p, Persistent (peerOk (GF := GF) p)) ∧
  (∀ hs, Persistent (healthAt (GF := GF) hs))

/-- An error grpc made itself is a status with one of grpc's own messages. -/
def ownErr_grpcMsg.spec : Prop := ∀ err,
  ownErr (GF := GF) err ⊢ ∃ code msg, statusErr err code msg ∗ ⌜grpcMsg msg⌝

/-- A handler's status error is sent as itself. -/
def statusErr_sent.spec : Prop := ∀ err code msg,
  statusErr (GF := GF) err code msg ⊢ sentStatus err code msg

/-- A context's error returned by a handler is sent as its status (`Canceled` or
`DeadlineExceeded`, with grpc's own message). -/
def ctxErr_sent.spec : Prop := ∀ err,
  context.isCtxErr (GF := GF) err ⊢ ∃ code msg, sentStatus err code msg ∗ ⌜grpcMsg msg⌝

/-- One status error, one code and message. -/
def statusErr_agree.spec : Prop := ∀ err c c' m m',
  statusErr (GF := GF) err c m ∗ statusErr err c' m' ⊢ ⌜c = c' ∧ m = m'⌝

/-- A run's context is a context the server's code may use. -/
def rpcCtx_ctxOk.spec : Prop := ∀ ctx md, rpcCtx (GF := GF) ctx md ⊢ Context.ctxOk ctx

/-- **The decoder**: decoding into a fresh (owned) message of the request's type gives the
request's content, canonical (grpc decodes the bytes it received; a request that fits decodes).
Closed world (A6 second tier): it never fails because the contents are those of this program's
clients, which `msgsFit` bounds; a foreign client's too-deep message would be refused by the
decoder (an error grpc makes, no run). -/
def decOk_call.spec : Prop := ∀ (dec : val) (reqT : go.GoType) (c c0 : Content) (q : Loc),
  {{ decOk (GF := GF) dec reqT c ∗ msgAt reqT q (DFrac.own 1) c0 }}
    (App (Val dec) (Val #(msgVal reqT q)))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil ∧ depth c < depthMax⌝ ∗
      msgAt reqT q (DFrac.own 1) c ∗ ⌜norm c = c⌝ }}

/-- **One attempt of a unary call** (grpc's invoker of `cc`, which an interceptor calls at most
once per attempt it wants): the request (read, given back) is delivered to at most one run of the
method's handler at an address the resolver reported, the caller's contract with it, for the
metadata the server sees (`ctx`'s outgoing metadata and the credentials'). It returns the run's
outcome (the reply decoded into the caller's holder, or the handler's status), or an error grpc
made itself, the contract then lost. -/
def attemptOk_call.spec : Prop := ∀ (cc : Loc) (A : GoString → IProp GF) (R : MD → IProp GF)
    (inv : val) (ctx : GoInterface) (m : GoString) (reqT repT : go.GoType) (S : UnarySpec (GF := GF))
    (pq : Loc) (dq : DFrac) (c : Content) (pr : Loc) (r0 : Content) (opts : GoSlice)
    (vs : List GoInterface) (md0 : MD) (Φ : Outcome → IProp GF),
  {{ attemptOk (GF := GF) cc A R inv ∗ Context.ctxOk ctx ∗ outMD ctx md0 ∗
      (□ ∀ ep, A ep -∗ serves ep m reqT repT S) ∗
      msgAt reqT pq dq c ∗ msgAt repT pr (DFrac.own 1) r0 ∗
      opts ↦*□ vs ∗ ([∗list] v ∈ vs, callOptOk v) ∗
      (∀ mdc md, □ R mdc -∗ ⌜mdSeen (mdc ++ md0) md⌝ -∗ S md (norm c) Φ) }}
    (App (App (App (App (App (App (Val inv) (Val #ctx)) (Val #m)) (Val #(msgVal reqT pq)))
      (Val #(msgVal repT pr))) (Val #cc)) (Val #opts))
  {{ (err : GoInterface), RET #err; msgAt reqT pq dq c ∗ ∃ r : Content, msgAt repT pr (DFrac.own 1) r ∗
      ((⌜err = GoInterface.nil⌝ ∗ Φ (.ok r)) ∨
       (∃ code msg, statusErr err code msg ∗ ⌜¬ grpcMsg msg⌝ ∗ Φ (.status code msg)) ∨
       ownErr err) }}

/-- **Opening a stream** (grpc's streamer of `cc`): a stream named `g` to one run of the method's
handler, the metadata `md` the server sees fixed now; both halves, nothing sent or received; or an
error grpc made itself. -/
def streamerOk_call.spec : Prop := ∀ (cc : Loc) (A : GoString → IProp GF) (R : MD → IProp GF)
    (str : val) (ctx : GoInterface) (desc : Loc) (m : GoString) (reqT repT : go.GoType)
    (S : StreamSpec (GF := GF)) (opts : GoSlice) (vs : List GoInterface) (md0 : MD),
  {{ streamerOk (GF := GF) cc A R str ∗ Context.ctxOk ctx ∗ outMD ctx md0 ∗
      (□ ∀ ep, A ep -∗ servesStream ep m reqT repT S) ∗
      opts ↦*□ vs ∗ ([∗list] v ∈ vs, callOptOk v) }}
    (App (App (App (App (App (Val str) (Val #ctx)) (Val #desc)) (Val #cc)) (Val #m)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (g : StreamName) (mdc md : MD), □ R mdc ∗ ⌜mdSeen (mdc ++ md0) md⌝ ∗
        streamKey g ∗ (∃ ctx', cliCtxOf cs ctx') ∗ cliSend cs g S md 0 ∗ cliRecv cs g S md 0) ∨
      (⌜cs = GoInterface.nil⌝ ∗ ownErr err) }}

/-- **`cs.SendMsg(m)`** (the `grpc.ClientStream` interface; the generated stubs' `Send`): the
message (read, given back) is the stream's next, with its `up` resource; or an error (the stream
broken, or ended by the server: then every later send fails), the resource lost. -/
def cliSend_send.spec : Prop := ∀ (cs : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF))
    (md : MD) (i : Nat) (reqT : go.GoType) (p : Loc) (dq : DFrac) (c : Content),
  {{ cliSend (GF := GF) cs g S md i ∗ msgAt reqT p dq c ∗ S.up g md i (norm c) }}
    (App (Val (cs @!! google_golang_org.grpc.ClientStream.ty @!! go!"SendMsg")) (Val #(msgVal reqT p)))
  {{ (err : GoInterface), RET #err; msgAt reqT p dq c ∗
      ((⌜err = GoInterface.nil⌝ ∗ cliSend cs g S md (i + 1)) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ (globalAddr io.EOF ↦□ err ∨ ownErr err) ∗ cliSend cs g S md (i + 1))) }}

/-- **`cs.CloseSend()`**: the client's half closed (the server's next receive after the `i`
messages is `io.EOF`). -/
def cliSend_closeSend.spec : Prop := ∀ (cs : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF))
    (md : MD) (i : Nat),
  {{ cliSend (GF := GF) cs g S md i }}
    (App (Val (cs @!! google_golang_org.grpc.ClientStream.ty @!! go!"CloseSend")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

/-- **`cs.RecvMsg(m)`** into an owned message of the reply type: the server's next message with its
`dn` resource; or the end: `io.EOF` (the handler returned `nil`) or the handler's status, with
`fin` at the number received (all the server sent); or an error grpc made itself. -/
def cliRecv_recv.spec : Prop := ∀ (cs : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF))
    (md : MD) (n : Nat) (repT : go.GoType) (p : Loc) (c0 : Content),
  {{ cliRecv (GF := GF) cs g S md n ∗ msgAt repT p (DFrac.own 1) c0 }}
    (App (Val (cs @!! google_golang_org.grpc.ClientStream.ty @!! go!"RecvMsg")) (Val #(msgVal repT p)))
  {{ (err : GoInterface), RET #err; ∃ c, msgAt repT p (DFrac.own 1) c ∗
      ((⌜err = GoInterface.nil ∧ norm c = c⌝ ∗ S.dn g md n c ∗ cliRecv cs g S md (n + 1)) ∨
       (globalAddr io.EOF ↦□ err ∗ S.fin g md n none) ∨
       (∃ code msg, statusErr err code msg ∗ ⌜¬ grpcMsg msg⌝ ∗ S.fin g md n (some (code, msg))) ∨
       ownErr err) }}

/-- **`st.RecvMsg(m)`** (the `grpc.ServerStream` interface): the client's next message with its
`up` resource; `io.EOF` once the client closed its half; or an error grpc made itself (the client
gone, the stream canceled). -/
def srvRecv_recv.spec : Prop := ∀ (st : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF))
    (md : MD) (i : Nat) (reqT : go.GoType) (p : Loc) (c0 : Content),
  {{ srvRecv (GF := GF) st g S md i ∗ msgAt reqT p (DFrac.own 1) c0 }}
    (App (Val (st @!! google_golang_org.grpc.ServerStream.ty @!! go!"RecvMsg")) (Val #(msgVal reqT p)))
  {{ (err : GoInterface), RET #err; ∃ c, msgAt reqT p (DFrac.own 1) c ∗
      ((⌜err = GoInterface.nil ∧ norm c = c⌝ ∗ S.up g md i c ∗ srvRecv st g S md (i + 1)) ∨
       (globalAddr io.EOF ↦□ err ∗ srvRecv st g S md i) ∨
       (ownErr err ∗ srvRecv st g S md i)) }}

/-- **`st.SendMsg(m)`**: the message (read, given back; grpc copies the encoding before
returning) is the stream's next, its `dn` resource with it; or an error grpc made itself (the
client gone), the resource lost. -/
def srvSend_send.spec : Prop := ∀ (st : GoInterface) (g : StreamName) (S : StreamSpec (GF := GF))
    (md : MD) (j : Nat) (repT : go.GoType) (p : Loc) (dq : DFrac) (c : Content),
  {{ srvSend (GF := GF) st g S md j ∗ msgAt repT p dq c ∗ S.dn g md j (norm c) }}
    (App (Val (st @!! google_golang_org.grpc.ServerStream.ty @!! go!"SendMsg")) (Val #(msgVal repT p)))
  {{ (err : GoInterface), RET #err; msgAt repT p dq c ∗
      ((⌜err = GoInterface.nil⌝ ∗ srvSend st g S md (j + 1)) ∨ (ownErr err ∗ srvSend st g S md j)) }}

/-- **`st.Context()`**: the run's context, from any goroutine (no half needed). -/
def srvStream_context.spec : Prop := ∀ (st ctx : GoInterface) (md : MD),
  {{ srvCtxOf (GF := GF) st ctx md }}
    (App (Val (st @!! google_golang_org.grpc.ServerStream.ty @!! go!"Context")) (Val #()))
  {{ RET #ctx; rpcCtx ctx md }}

/-- **`cs.Context()`**: the stream's context, from any goroutine. -/
def cliStream_context.spec : Prop := ∀ (cs ctx : GoInterface),
  {{ cliCtxOf (GF := GF) cs ctx }}
    (App (Val (cs @!! google_golang_org.grpc.ClientStream.ty @!! go!"Context")) (Val #()))
  {{ RET #ctx; Context.ctxOk ctx }}

/-- **The generic wrappers' methods are the stream's** (WP form): `Send(m)` is `SendMsg(m)`;
`Recv()` allocates a `new(T)` and `RecvMsg`s into it, returning it on success, `nil` otherwise;
`CloseSend` and `Context` are the embedded stream's. -/
def genCli_send.spec : Prop := ∀ (w : Loc) (cs : GoInterface) (reqT repT : go.GoType) (p : Loc)
    (Ψ : val → IProp GF),
  genCliAt (GF := GF) w cs reqT repT ∗
    WP (App (Val (cs @!! google_golang_org.grpc.ClientStream.ty @!! go!"SendMsg")) (Val #(msgVal reqT p))) {{ Ψ }} ⊢
  WP (App (Val (w @!! go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty reqT repT) @!! go!"Send")) (Val #p)) {{ Ψ }}

def genCli_closeSend.spec : Prop := ∀ (w : Loc) (cs : GoInterface) (reqT repT : go.GoType)
    (Ψ : val → IProp GF),
  genCliAt (GF := GF) w cs reqT repT ∗
    WP (App (Val (cs @!! google_golang_org.grpc.ClientStream.ty @!! go!"CloseSend")) (Val #())) {{ Ψ }} ⊢
  WP (App (Val (w @!! go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty reqT repT) @!! go!"CloseSend")) (Val #())) {{ Ψ }}

def genCli_recv.spec : Prop := ∀ (w : Loc) (cs : GoInterface) (reqT repT : go.GoType)
    (Ψ : val → IProp GF),
  genCliAt (GF := GF) w cs reqT repT ∗
    (∀ (p : Loc) (c0 : Content), msgAt repT p (DFrac.own 1) c0 -∗
      WP (App (Val (cs @!! google_golang_org.grpc.ClientStream.ty @!! go!"RecvMsg")) (Val #(msgVal repT p)))
        {{ v, ∀ err : GoInterface, ⌜v = #err⌝ -∗
            Ψ (PairV #(if decide (err = GoInterface.nil) then p else null) #err) }}) ⊢
  WP (App (Val (w @!! go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty reqT repT) @!! go!"Recv")) (Val #())) {{ Ψ }}

def genSrv_send.spec : Prop := ∀ (w : Loc) (st : GoInterface) (reqT repT : go.GoType) (p : Loc)
    (Ψ : val → IProp GF),
  genSrvAt (GF := GF) w st reqT repT ∗
    WP (App (Val (st @!! google_golang_org.grpc.ServerStream.ty @!! go!"SendMsg")) (Val #(msgVal repT p))) {{ Ψ }} ⊢
  WP (App (Val (w @!! go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty reqT repT) @!! go!"Send")) (Val #p)) {{ Ψ }}

def genSrv_recv.spec : Prop := ∀ (w : Loc) (st : GoInterface) (reqT repT : go.GoType)
    (Ψ : val → IProp GF),
  genSrvAt (GF := GF) w st reqT repT ∗
    (∀ (p : Loc) (c0 : Content), msgAt reqT p (DFrac.own 1) c0 -∗
      WP (App (Val (st @!! google_golang_org.grpc.ServerStream.ty @!! go!"RecvMsg")) (Val #(msgVal reqT p)))
        {{ v, ∀ err : GoInterface, ⌜v = #err⌝ -∗
            Ψ (PairV #(if decide (err = GoInterface.nil) then p else null) #err) }}) ⊢
  WP (App (Val (w @!! go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty reqT repT) @!! go!"Recv")) (Val #())) {{ Ψ }}

def genCli_context.spec : Prop := ∀ (w : Loc) (cs ctx : GoInterface) (reqT repT : go.GoType),
  {{ genCliAt (GF := GF) w cs reqT repT ∗ cliCtxOf cs ctx }}
    (App (Val (w @!! go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty reqT repT) @!! go!"Context")) (Val #()))
  {{ RET #ctx; Context.ctxOk ctx }}

def genSrv_context.spec : Prop := ∀ (w : Loc) (st ctx : GoInterface) (md : MD) (reqT repT : go.GoType),
  {{ genSrvAt (GF := GF) w st reqT repT ∗ srvCtxOf st ctx md }}
    (App (Val (w @!! go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty reqT repT) @!! go!"Context")) (Val #()))
  {{ RET #ctx; rpcCtx ctx md }}

/-- A context with no outgoing metadata (W0's `ctxNoMeta`) has none. -/
def outMD_noMeta.spec : Prop := ∀ ctx, Context.ctxNoMeta (GF := GF) ctx ⊢ outMD ctx []

/-- Every context has its outgoing metadata (what `FromOutgoingContext` reads), one. -/
def outMD_ctxOk.spec : Prop := ∀ ctx, Context.ctxOk (GF := GF) ctx ⊢ ∃ md, outMD ctx md
def outMD_agree.spec : Prop := ∀ ctx md md',
  outMD (GF := GF) ctx md ∗ outMD ctx md' ⊢ ⌜md = md'⌝

/-- A child context (`WithCancel`, `WithTimeout`) and a `WithValue` at another key keep it. -/
def outMD_child.spec : Prop := ∀ ctx ctx' md,
  outMD (GF := GF) ctx md ∗ Context.ctxChild ctx ctx' ⊢ outMD ctx' md
def outMD_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk) md,
  outMD (GF := GF) ctx md ∗ Context.ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ google_golang_org.grpc.metadata.mdOutgoingKey.ty⌝ ⊢ outMD ctx' md

def mdAt_persist.spec : Prop := ∀ m md, mdAt (GF := GF) m (DFrac.own 1) md ⊢ |==> mdAt m DFrac.discard md
def mdAt_discard_persistent.spec : Prop := ∀ m md, Persistent (mdAt (GF := GF) m DFrac.discard md)

/-- **A server's registrations meet the contracts `C`**: each registered handler meets the
contract `C` gives its method, under the server's interceptor chain, each run with the run
resource `T` (persistent). -/
def regsOk (B : SrvCfg) (C : AddrContract (GF := GF)) (T : IProp GF) : IProp GF :=
  iprop(([∗list] r ∈ B.regs, ∃ (reqT repT : go.GoType) (S : UnarySpec (GF := GF)),
      ⌜C.unary r.1 = some (reqT, repT, S)⌝ ∗ □ ∀ ic, icChain B.ics ic -∗ unaryOk r.2.1 r.2.2 ic reqT repT S T) ∗
    ([∗list] r ∈ B.sregs, ∃ (reqT repT : go.GoType) (S : StreamSpec (GF := GF)),
      ⌜C.stream r.1 = some (reqT, repT, S)⌝ ∗ □ ∀ sic, icChain B.sics sic -∗
        streamOk r.2.1 r.2.2 (if B.sics = [] then none else some sic) reqT repT S T))

/-- `grpcOver` fixes its contracts. (Integration I3: 2a's round-1 request of 2f's
`protoAt_agree : protoAt a P ∗ protoAt a P' ⊢ ⌜P = P'⌝` is withdrawn: a protocol holds `IProp`s, so
a ghost agreement on it gives at most a later equivalence, and no client composes two bindings of
one address; that a member's server and its clients see one contract per address is part of this
boundary's assumed realization, `addrAt`'s.) -/
def grpcOver_inj.spec : Prop := ∀ (C C' : AddrContract (GF := GF)) (P P' : Http.Proto GF),
  grpcOver C P = grpcOver C' P' → C = C' ∧ P = P'

/-- **Requests that are not gRPC calls are `P`'s** (what net/http's other handlers on the socket
serve). -/
def grpcOver_other.spec : Prop := ∀ (C : AddrContract (GF := GF)) (P : Http.Proto GF) (R : Http.HReq)
    (τ : GName),
  ¬ grpcReq R → ((grpcOver C P).hreq R τ ⊣⊢ P.hreq R τ) ∧
    (∀ B, (grpcOver C P).body R τ B ⊣⊢ P.body R τ B) ∧
    (∀ B, (grpcOver C P).bodyPre R τ B ⊣⊢ P.bodyPre R τ B) ∧
    (∀ st hs w, (grpcOver C P).resp R τ st hs w ⊣⊢ P.resp R τ st hs w)

/-- **cmux's split** of a bound listener: its HTTP/1 part (no gRPC call: grpc requires HTTP/2) and
its HTTP/2 part. -/
def cmux_split.spec : Prop := ∀ (l : GoInterface) (ep : GoString),
  Http.listenerAt (GF := GF) l ep ⊢ |==> ∃ l1 l2, cmuxSubAt l1 ep false ∗ cmuxSubAt l2 ep true

/-- cmux's HTTP/1 part is a listener net/http serves at `ep`. -/
def cmux_http1.spec : Prop := ∀ (l : GoInterface) (ep : GoString),
  cmuxSubAt (GF := GF) l ep false ⊢ Http.listenerAt l ep

/-- **Starting to serve** (a ghost step before `Serve`): a server built with the registrations of
`B` (grpc's health service's among them), a listener at `ep` (or cmux's HTTP/2 part of one) whose
address is bound to `C`, each registration's handler meeting the contract `C` gives its method
(under the server's interceptor chain), a pool of the caller's thread tokens for the runs (2f's
`Http.handlerPool`, from `threadToks n`: each run draws one for its life and returns it; the
physical premise: grpc runs at most `n` handlers of this server at once, a bound the adequacy
theorem fixes), and the workload premise. Gives the right to run `Serve`. **The run resource**
(integration X): `n` copies of the caller's `T`, one lent to each run with its thread token and given
back when it returns; `GracefulStop` (which waits for the runs) gives them back (`drainTok`). An
etcd member lends each run a share of 2e's `srvGate` (`v3rpc/Api.lean`'s `HandlerTriple`). -/
def start.spec : Prop := ∀ (gs : Loc) (B : SrvCfg) (lis : GoInterface) (ep : GoString)
    (C : AddrContract (GF := GF)) (pl : GName) (n : Nat) (T : IProp GF),
  srvBuild gs B ∗ grpcListener lis ep ∗ addrAt ep C ∗ Http.handlerPool pl n ∗ ⌜msgsFit⌝ ∗
    ([∗list] _u ∈ List.replicate n (), T) ∗ regsOk B C T ⊢
  |==> serveTok gs lis ∗ drainTok gs T n

/-- **Starting to serve through net/http** (etcd's TLS path): no listener and no pool (the runs are
net/http's handler runs, with their tokens); no run resource (`emp`: net/http's pool lends none, and
`GracefulStop` does not wait for `ServeHTTP`'s runs; integration X: a handler that needs one, an etcd
handler over 2c's request path and its `srvGate` share, cannot be served this way: recorded). -/
def startHTTP.spec : Prop := ∀ (gs : Loc) (B : SrvCfg) (C : AddrContract (GF := GF)),
  srvBuild gs B ∗ ⌜msgsFit⌝ ∗ regsOk B C iprop(emp) ⊢ |==> servesHTTP gs C

def round1_persistent.spec : Prop :=
  (∀ err, Persistent (plainErr (GF := GF) err)) ∧
  (∀ gs C, Persistent (servesHTTP (GF := GF) gs C)) ∧
  (∀ st ctx md, Persistent (srvCtxOf (GF := GF) st ctx md)) ∧
  (∀ cs ctx, Persistent (cliCtxOf (GF := GF) cs ctx)) ∧
  (∀ w cs t t', Persistent (genCliAt (GF := GF) w cs t t')) ∧
  (∀ w st t t', Persistent (genSrvAt (GF := GF) w st t t')) ∧
  (∀ p, Persistent (peerVar (GF := GF) p))

def srvBuild_ne_null.spec : Prop := ∀ gs B, srvBuild (GF := GF) gs B ⊢ ⌜gs ≠ null⌝

/-- **What a status error is**: it prints `grpcText` (never empty), it is a `*status.Error`
(`internal/status.Error`: neither an `EtcdError` nor a context's error; its `Is(target)` is true
only of a `*status.Error` with an equal status), and it is comparable. -/
def statusErr_errMsg.spec : Prop := ∀ err c m,
  statusErr (GF := GF) err c m ⊢ errMsg err (grpcText c m)

def statusErr_ty.spec : Prop := ∀ err c m,
  statusErr (GF := GF) err c m ⊢
    ⌜cmpErr err ∧ ∃ v, err = interface.mkOk (go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty) v⌝

/-- **The incoming metadata's keys have values** (grpc decodes no empty header). -/
def rpcCtx_vals.spec : Prop := ∀ ctx md, rpcCtx (GF := GF) ctx md ⊢ ⌜∀ e ∈ md, e.2 ≠ []⌝

/-- **`mdAt`'s meaning**: Perennial's map points-to, each key's slice read-only with the key's
values (what the map lookups `md[k]` of the interceptors and the auth store read). -/
def mdAt_ownMap.spec : Prop := ∀ (m : Loc) (dq : DFrac) (md : MD),
  mdAt (GF := GF) m dq md ⊣⊢ ∃ mm : GMap GoString GoSlice, ownMap m dq mm ∗
    (□ ∀ (k : GoString) (sl : GoSlice), ⌜mm.lookup k = some sl⌝ -∗ sl ↦*□ md.get k) ∗
    ⌜∀ k, mm.lookup k = none → md.get k = []⌝

/-- **The chain's call** (WP form): the chained interceptor runs the first interceptor with a
continuation running the rest, then the handler `h`; with no interceptor grpc passes `nil` and the
generated handler calls the method itself (`icChain [] ic`: `ic` is the nil function). -/
def icChain_call.spec : Prop := ∀ (i : GoFunc) (ics : List GoFunc) (ic : val) (ctx req : GoInterface)
    (info : Loc) (h : val) (Ψ : val → IProp GF),
  icChain (GF := GF) (i :: ics) ic ∗
    (∀ k, icHandler ics info k h -∗
      WP (App (App (App (App (Val #i) (Val #ctx)) (Val #req)) (Val #info)) (Val k)) {{ Ψ }}) ⊢
  WP (App (App (App (App (Val ic) (Val #ctx)) (Val #req)) (Val #info)) (Val h)) {{ Ψ }}

/-- **No interceptor**: grpc passes the `nil` function (verify-round, A6 second tier: the
docstring of `icChain_call` said so, no law did). -/
def icChain_nil.spec : Prop := ∀ (ic : val), icChain (GF := GF) [] ic ⊢ ⌜ic = #func.nil⌝

/-- **A continuation's call**: the next interceptor with the next continuation, or (none left) the
handler. -/
def icHandler_call.spec : Prop := ∀ (ics : List GoFunc) (info : Loc) (k h : val) (ctx req : GoInterface)
    (Ψ : val → IProp GF),
  icHandler (GF := GF) ics info k h ∗
    (match ics with
     | [] => WP (App (App (Val h) (Val #ctx)) (Val #req)) {{ Ψ }}
     | i :: rest => ∀ (k' : val), icHandler rest info k' h -∗
         WP (App (App (App (App (Val #i) (Val #ctx)) (Val #req)) (Val #info)) (Val k')) {{ Ψ }}) ⊢
  WP (App (App (Val k) (Val #ctx)) (Val #req)) {{ Ψ }}

/-! ### Any context's incoming metadata and peer (integration I3) -/

def ctxInMD_persistent.spec : Prop :=
  (∀ ctx o, Persistent (ctxInMD (GF := GF) ctx o)) ∧ (∀ ctx c, Persistent (ctxPeerCN (GF := GF) ctx c))

/-- One context, one incoming metadata, one peer identity. -/
def ctxInMD_agree.spec : Prop :=
  (∀ ctx o o', ctxInMD (GF := GF) ctx o ∗ ctxInMD ctx o' ⊢ ⌜o = o'⌝) ∧
  (∀ ctx c c', ctxPeerCN (GF := GF) ctx c ∗ ctxPeerCN ctx c' ⊢ ⌜c = c'⌝)

/-- **A run's context**: its incoming metadata is the run's (grpc decoded it), and it has a peer
identity (the connection's). -/
def rpcCtx_inMD.spec : Prop := ∀ ctx md,
  rpcCtx (GF := GF) ctx md ⊢ ctxInMD ctx (some md) ∗ ∃ c, ctxPeerCN ctx c

/-- `Background()` carries neither. -/
def ctxInMD_background.spec : Prop :=
  ⊢ ctxInMD (GF := GF) (GoInterface.ok context.backgroundCtxVal) none ∗
    ctxPeerCN (GoInterface.ok context.backgroundCtxVal) none

/-- A child context (`WithCancel`, `WithTimeout`) keeps both. -/
def ctxInMD_child.spec : Prop := ∀ ctx ctx' o c,
  ctxInMD (GF := GF) ctx o ∗ ctxPeerCN ctx c ∗ Context.ctxChild ctx ctx' ⊢ ctxInMD ctx' o ∗ ctxPeerCN ctx' c

/-- A `WithValue` at another key than the incoming metadata's and the peer's keeps both. -/
def ctxInMD_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk) o c,
  ctxInMD (GF := GF) ctx o ∗ ctxPeerCN ctx c ∗ Context.ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ google_golang_org.grpc.metadata.mdIncomingKey.ty ∧
      ki.ty ≠ google_golang_org.grpc.peer.peerKey.ty⌝ ⊢ ctxInMD ctx' o ∗ ctxPeerCN ctx' c

end res

end Grpc
end EtcdGrove
end Perennial
