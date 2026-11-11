/-
**grpc's runs on real forks** (per-type stage B, B1a, 2026-11-11; Scope r5 §2.1-2.2,
`/shared/tmp/stageB/scope-r5.md`; Lean-first, no Rocq counterpart). The vocabulary of the trusted
`Serve` model (`TrustedCode/google_golang_org/grpcServeModel.lean`) and of its leaves' axioms
(`Spec/google_golang_org/grpc/model/`), which replace `grpc.serve`/`grpc.serveStream`'s
caller-chosen run resource and count (`axiom/grpc-serve-pool`, `1ad2cc63a0`) in B1b. B1a adds these
names beside the old ones; nothing outside this file, the model, its leaves and the `Serve` theorem
uses them yet.

**Go's configuration as a trusted fact.** `grpc.start` (restated in B1b) emits, from the server
being built (`grpcSrvNew gs ics sics svcs regs sregs`), a persistent `grpcSrvCfg γ c`: the chains and
registrations Go's server holds (`GrpcSrvCfg`), fixed from `Serve` on (grpc's `RegisterService`
after `Serve` is fatal), beside `grpcAddrIs addr γ` (the server listening at `addr` is `γ`) and the
exclusive `grpcSrvLink gs lis γ` (the right to accept `γ`'s calls on `lis`). A proof cannot choose
`c`: it is made only by `grpc.start`, from `grpcSrvNew`, and is unique per `γ`
(`grpcSrvCfg_agree`); `γ` is unique per address (`grpcAddrIs_agree`).

**The registration** of a method at a server (`isGrpcRpcAt γ name Spec`): Go's configuration lists
`(name, mh, srv)` and the handler meets `Spec` under Go's chain, each run given the literal
`threadTok` and one later credit and returning the token (`grpcRunOkMd`, the run contract). No
caller-chosen resource, no count, no ghost registry, no saved predicate.

**The pair** (the soundness argument of the five trusted texts `ClientConn.Invoke`,
`ClientConn.NewStream`, `acceptRun`, `acceptRunConns`, `respond`, which are one channel per call):
- **Unary.** `Invoke`'s pre gives up the registration of the method at the address its attempt
  reaches (`grpcAddrIs a γ ∗ isGrpcRpcAt γ method Spec`) and `▷ Spec md m Φ Ψe` at the attempt's
  metadata. The server that accepts the attempt is the one listening at `a` (TCP; `bridge.New` maps
  a bridge's address to its target's `γ`), so it is `γ` (`grpcAddrIs_agree`), and the run's context
  carries the attempt's metadata. `acceptRun` hands exactly these to the run (the conjuncts of
  `grpcAccepted` marked "deposited") and a `grpcReplyTo` for `Φ`/`Ψe`. `respond` consumes `Φ m'`
  (or `Ψe d`) with the reply, and `Invoke`'s success post returns that `Φ m'` (its error post returns
  `Ψe d` only for a `handlerDescs` description, which only the handler makes).
- **One deposit, one run.** A deposit reaches at most one run: (a) grpc's transparent retry resends
  only a stream the server never processed (`stream.go`, `shouldRetry`'s unprocessed case); (b) the
  program's clients have no retry policy, no hedging and no `healthCheckConfig`: every client is
  made by the `NewClient` spec under `grpcResolverAt` (a service config without a retry policy) and
  `dialOptsAt`; without (b) grpc does resend a processed trailers-only attempt
  (`stream.go:803-858`; test T8b), which is why it is cited; (c) the world premise D7: every client
  connection to a served address is one the `NewClient` spec made (`grpcConn`), and grpc makes no
  calls of its own (no client-side health checks, no ORCA out-of-band streams). So each deposit is
  handed to at most one run, and `grpcReplyTo` (exclusive, no laws) is consumed once. An `Invoke`
  that returns an error early leaves its deposit with the run (grpc's handler runs asynchronously,
  test T2): nothing returns a deposit to a client.
- **Streams.** `NewStream`'s post and the server end share the stream's names `γs`, `Dn` and the
  persistent `Spec md γs Dn`; the server half is `acceptRun`'s stream arm, and the stream
  registration (`isGrpcStreamAt`) is deposited as in the unary case.
- **Go facts, not pair facts:** `(name, mh, srv) ∈ c.regs` (Go's dispatch), `grpcSrvChain c.ics`
  and `grpcSrvStreamChain c.sics` (Go's chains), `grpcDecOk` (grpc's codec), `grpcRunCtx` (no etcd
  keys in a run's context).

What the carrier (`Serve`'s proof) proves from this: `grpcSrvCfg_agree` makes the deposit's
configuration Go's `c`; the joint `Nodup` of `c.regs ++ c.sregs`' names (`grpc.start`'s premise,
carried by `grpcSrvNodup`) makes the deposit's handler Go's; the deposit's run contract then applies
to Go's handler with the carrier's own fork token and credit (`wp_fork_tok_upd`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import TrustedCode.google_golang_org.grpcServeModel
public import Perennial.Proof.ThreadPool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-! ## Go's configuration of a server -/

section cfg
variable [GooseExts]

/-- **Go's configuration of one gRPC server**: the unary and stream interceptor chains
`grpc.NewServer`'s options compose (`ics`, `sics`), and the `(full method name, handler, service
value)` of every registered method (`regs`) and stream (`sregs`) (`RegisterService`). -/
structure GrpcSrvCfg (GF : BundledGFunctors) where
  ics : List GoFunc
  sics : List GoFunc
  regs : List (GoString × val × GoInterface)
  sregs : List (GoString × val × GoInterface)

/-- **The full names of `c`'s methods and streams are jointly distinct** (`grpc.start`'s premise, M1:
what makes the one entry named by a call's path the handler Go's split lookup finds). -/
def grpcSrvNodup {GF : BundledGFunctors} (c : GrpcSrvCfg GF) : Prop :=
  ((c.regs ++ c.sregs).map Prod.fst).Nodup

end cfg

/-- **The server listening at `addr` is `γ`** (raw; see `grpcAddrIs`). Made only by `grpc.start` (and
carried to a bridge's address by `bridge.New`). -/
axiom grpcAddrIsRaw {GF : BundledGFunctors} (addr : List w8) (γ : GName) : IProp GF

/-- **Server `γ` was built with Go's configuration `c`** (raw). Made only by `grpc.start`, from
`grpcSrvNew gs c.ics c.sics _ c.regs c.sregs`: no registration is made after `Serve` starts (grpc
logs fatally on `RegisterService` after `Serve`, `server.go` `RegisterService`/`register`). -/
axiom grpcSrvCfgRaw {GF : BundledGFunctors} [GooseExts] (γ : GName) (c : GrpcSrvCfg GF) : IProp GF

/-- **The right to accept `γ`'s calls on `lis` through `gs`** (exclusive; made only by `grpc.start`,
consumed by `acceptRun`'s `lisFailed` arm). -/
axiom grpcSrvLink {GF : BundledGFunctors} [GooseExts] (gs : Loc) (lis : GoInterface) (γ : GName) :
  IProp GF

/-- **The right to accept further calls on `gs`'s already-open connections** after its listener
failed (exclusive; made only by `acceptRun`'s `lisFailed` arm, once per `gs`). -/
axiom grpcConnsLink {GF : BundledGFunctors} (gs : Loc) (γ : GName) : IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server listening at `addr` is `γ`** (persistent by construction). -/
def grpcAddrIs (addr : GoString) (γ : GName) : IProp GF := iprop(□ grpcAddrIsRaw addr γ)

instance grpcAddrIs_persistent (addr : GoString) (γ : GName) :
    Persistent (grpcAddrIs (GF := GF) addr γ) := by
  unfold grpcAddrIs; infer_instance

/-- **Server `γ` was built with Go's configuration `c`** (persistent by construction). -/
def grpcSrvCfg (γ : GName) (c : GrpcSrvCfg GF) : IProp GF := iprop(□ grpcSrvCfgRaw γ c)

instance grpcSrvCfg_persistent (γ : GName) (c : GrpcSrvCfg GF) :
    Persistent (grpcSrvCfg (GF := GF) γ c) := by
  unfold grpcSrvCfg; infer_instance

end defs

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **One server per address.** True: `netAddrFree` allows one `Listen` per address in a run
(`Proof/net/InvNet.lean`), `grpc.start` consumes the listener, and `bridge.New` consumes the
bridge's own listener. (Restart's S10 must revisit this if a `Stop` spec ever frees an address.) -/
axiom grpcAddrIs_agree (addr : GoString) (γ γ' : GName) :
  grpcAddrIs (GF := GF) addr γ ∗ grpcAddrIs addr γ' ⊢ ⌜γ = γ'⌝

/-- **One configuration per server**: `grpc.start` makes `grpcSrvCfg γ _` once per `γ`. -/
axiom grpcSrvCfg_agree (γ : GName) (c c' : GrpcSrvCfg GF) :
  grpcSrvCfg (GF := GF) γ c ∗ grpcSrvCfg γ c' ⊢ ⌜c = c'⌝

/-- **The reply channel of the accepted unary call `r`**, back to the client whose `Invoke`
deposited `Φ`, `Ψe` (exclusive; made only by `acceptRun`/`acceptRunConns`; its only use is
`respond`'s pre; no law). -/
axiom grpcReplyTo (r : val) (Rep : ProtoMsgT GF) (Φ : Rep.M → IProp GF)
  (Ψe : GoString → IProp GF) : IProp GF

end axioms

/-! ## The run contracts -/

section run
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The run contract of a unary handler**: `grpcMethodOkMd`'s text with the per-run resource fixed
to what a run is given, the fork's thread token and later credit (`wp_fork_tok_upd`), in the pre, and
the token in the post. A run, given the token and the credit, the run's context (`isContext`,
`grpcRunCtx`), grpc's `dec` for the request at `m`, the chain's interceptor (`grpcSrvChain`) and
`Spec md m Φ Ψe` at the context's incoming metadata, returns the token and, on success, a response
`*T` (as `any`) at some `m'` with `Φ m'`, on a handler's error its `Ψe`, and an error grpc's
`status.FromError` takes. Handlers are proved against `grpcMethodOkMd` at their bundle; the adapters
(`grpcRunOkMd_of_pools`) give this contract. -/
def grpcRunOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ threadTok ∗ £ 1 ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
        grpcSrvChain ics ui ∗ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); threadTok ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
          Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcRunOkMd_persistent {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep) :
    Persistent (grpcRunOkMd mh srv ics Spec) := by
  unfold grpcRunOkMd; infer_instance

/-- **The run contract of a stream handler**: `grpcStreamMethodOk`'s text with the per-run resource
fixed to the fork's thread token and later credit, and the post returning the token: the stream
specification is satisfiable per stream (`streamSpecOk`, at every metadata), and a run, given
`Spec md γ Dn` at its context's metadata, the token and the credit, the run's raw server end (both
tokens at `[]`) and grpc's `info`, through the chain, terminates or not, returning an error grpc's
`status` takes and the token. -/
def grpcStreamRunOk {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface) (sics : List GoFunc)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) : IProp GF :=
  iprop((□ ∀ md, streamSpecOk (Spec md)) ∗
    □ ∀ (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (info : Loc),
      Spec (metadata.incomingOf (GoInterface.ok ci)) γ Dn -∗ threadTok -∗ £ 1 -∗
      srvRawStreamIs st γ Req Rep Up Dn ci cd -∗
      srvRecvTok (Req := Req) γ [] -∗ srvSendTok (Rep := Rep) γ [] -∗ streamAuxTok γ -∗
      srvStreamInfoIs info -∗
      srvStreamChainWP #info sics mh #srv #st
        (fun v => iprop(∃ err : GoInterface, ⌜v = #err⌝ ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗
          threadTok)))

instance grpcStreamRunOk_persistent {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface)
    (sics : List GoFunc) (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) :
    Persistent (grpcStreamRunOk mh srv sics Up Spec) := by
  unfold grpcStreamRunOk; infer_instance

/-- A run contract at a spec is one at a stronger spec. -/
theorem grpcRunOkMd_mono {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ Spec md m Φ Ψe) :
    grpcRunOkMd mh srv ics Spec ⊢ grpcRunOkMd mh srv ics Spec' := by
  iintro #Hm
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HT Hlc Hctx Hrc Hd Hch HSpec] HΨ
  iframe
  iapply (h _ m Φ Ψe) $$ HSpec

/-- A run contract at a spec is one at a spec that gives it after an update. -/
theorem grpcRunOkMd_mono_upd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ |==> Spec md m Φ Ψe) :
    grpcRunOkMd mh srv ics Spec ⊢ grpcRunOkMd mh srv ics Spec' := by
  iintro #Hm
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  ihave HSpec := (h _ m Φ Ψe) $$ HSpec
  imod HSpec
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HT Hlc Hctx Hrc Hd Hch HSpec] HΨ
  iframe

end run

/-! ## The registration and the accepted call -/

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The registration of `name` at server `γ`, as Go has it**: Go's configuration `c` lists
`(name, mh, srv)`, and the handler meets `Spec` under Go's chain, each run given a thread token and
one later credit and returning the token (`grpcRunOkMd`). -/
def isGrpcRpcAt {Req Rep : ProtoMsg GF} (γ : GName) (name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∃ (c : GrpcSrvCfg GF) (mh : val) (srv : GoInterface),
    grpcSrvCfg γ c ∗ ⌜(name, mh, srv) ∈ c.regs⌝ ∗ □ grpcRunOkMd mh srv c.ics Spec)

instance isGrpcRpcAt_persistent {Req Rep : ProtoMsg GF} (γ : GName) (name : GoString)
    (Spec : GrpcSpecMd Req Rep) : Persistent (isGrpcRpcAt γ name Spec) := by
  unfold isGrpcRpcAt; infer_instance

/-- **The registration of the stream `name` at server `γ`, as Go has it** (the stream analogue of
`isGrpcRpcAt`, with `grpcStreamRunOk`). -/
def isGrpcStreamAt {Req Rep : StreamMsg GF} (γ : GName) (name : GoString)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) : IProp GF :=
  iprop(∃ (c : GrpcSrvCfg GF) (mh : val) (srv : GoInterface),
    grpcSrvCfg γ c ∗ ⌜(name, mh, srv) ∈ c.sregs⌝ ∗ grpcStreamRunOk mh srv c.sics Up Spec)

instance isGrpcStreamAt_persistent {Req Rep : StreamMsg GF} (γ : GName) (name : GoString)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) :
    Persistent (isGrpcStreamAt γ name Up Spec) := by
  unfold isGrpcStreamAt; infer_instance

/-- **The composed stream interceptor grpc calls, for the chain `sics`** (persistent; as
`grpcSrvChain` for streams: grpc's `chainStreamServerInterceptors`, `server.go:1245-1262`: `nil` for
no interceptor, the one interceptor, or grpc's closure). The handler `h` is any value (a
`StreamDesc.Handler`), as `srvStreamChainWP` takes it. -/
def grpcSrvStreamChain (sics : List GoFunc) (si : GoFunc) : IProp GF :=
  match sics with
  | [] => iprop(⌜si = func.nil⌝)
  | _ :: _ => iprop(⌜si ≠ func.nil⌝ ∗ □ ∀ (srv st info h : val) (Ψ : val → IProp GF),
      srvStreamChainWP info sics h srv st Ψ -∗
      WP (App (App (App (App (Val #si) (Val srv)) (Val st)) (Val info)) (Val h)) {{ Ψ }})

instance grpcSrvStreamChain_persistent (sics : List GoFunc) (si : GoFunc) :
    Persistent (grpcSrvStreamChain (GF := GF) sics si) := by
  unfold grpcSrvStreamChain; cases sics <;> infer_instance

/-- **An accepted call** `r` of server `γ` with Go's configuration `c` (what `acceptRun` returns
with `runOk`). Unary: the run value of Go's handler `(name, mh, srv) ∈ c.regs` for the call's path;
the registration the client deposited (`isGrpcRpcAt γ name Spec`) and its request precondition
`▷ Spec md m Φ Ψe` at the metadata the run's context carries; grpc's context, decoder and chain
(Go facts); the reply channel `grpcReplyTo r Rep Φ Ψe`. Stream: the run value of Go's handler
`(name, mh, srv) ∈ c.sregs`, a function value (not a panic: grpc passes it to the interceptor as
an argument); the deposited stream registration; Go's composed stream interceptor;
the stream's shared persistent `Spec md γs Dn` and its raw server end with both tokens at `[]`;
grpc's `info`. -/
def grpcAccepted (γ : GName) (c : GrpcSrvCfg GF) (r : val) : IProp GF :=
  iprop((∃ (name : GoString) (mh : val) (srv : GoInterface) (ci : GoInterfaceOk)
        (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc) (Req Rep : ProtoMsgT GF)
        (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M) (Φ : Rep.M → IProp GF)
        (Ψe : GoString → IProp GF),
      ⌜r = google_golang_org.grpc.model.runUnary mh srv ci dec ui⌝ ∗ ⌜(name, mh, srv) ∈ c.regs⌝ ∗
      isGrpcRpcAt γ name Spec ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req.toProtoMsg m ∗
      grpcSrvChain c.ics ui ∗
      ▷ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe ∗
      grpcReplyTo r Rep Φ Ψe) ∨
    (∃ (name : GoString) (mh : val) (srv : GoInterface) (ci : GoInterfaceOk)
        (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (info : Loc) (si : GoFunc)
        (Req Rep : StreamMsgT GF) (Up : Nat → Req.M → IProp GF)
        (Spec : GrpcMd → StreamSpec Rep.toStreamMsg) (γs : StreamNames)
        (Dn : Nat → Rep.M → IProp GF),
      ⌜r = google_golang_org.grpc.model.runStream mh srv st info ci si⌝ ∗
      ⌜(name, mh, srv) ∈ c.sregs⌝ ∗ ⌜mh.isPanic = false⌝ ∗
      isGrpcStreamAt γ name Up Spec ∗
      grpcSrvStreamChain c.sics si ∗
      □ Spec (metadata.incomingOf (GoInterface.ok ci)) γs Dn ∗
      srvRawStreamIs st γs Req.toStreamMsg Rep.toStreamMsg Up Dn ci cd ∗
      srvRecvTok (Req := Req.toStreamMsg) γs [] ∗ srvSendTok (Rep := Rep.toStreamMsg) γs [] ∗
      streamAuxTok γs ∗ srvStreamInfoIs info))

/-- **The right to serve `gs` on `lis` as server `γ`** (B1a's name; B1b makes it `grpcServeTok`,
replacing the old axiom): the link, Go's configuration, and the replies' size premise under which
`grpc.start` made them. -/
def grpcServeTokR (gs : Loc) (lis : GoInterface) (γ : GName) : IProp GF :=
  iprop(grpcSrvLink gs lis γ ∗ (∃ c : GrpcSrvCfg GF, grpcSrvCfg γ c ∗ ⌜grpcSrvNodup c⌝) ∗
    ⌜grpcRepliesFit⌝)

end reg

/-! ## The adapters: a handler's bundle from leveled pools -/

section adapt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Levels 0 to 3 of a thread token, and the rest. -/
theorem threadTok_levels0123 (HT : 4 ≤ threadBound GF) :
    threadTok (GF := GF) ⊣⊢ levelTok 0 ∗ levelTok 1 ∗ levelTok 2 ∗ levelTok 3 ∗ threadTokFrom 4 := by
  constructor
  · iintro H
    icases (threadTok_level0 (GF := GF)).1 $$ H with ⟨H0, H⟩
    icases (threadTokFrom_succ (GF := GF) 1 (by omega)).1 $$ H with ⟨H1, H⟩
    icases (threadTokFrom_succ (GF := GF) 2 (by omega)).1 $$ H with ⟨H2, H⟩
    icases (threadTokFrom_succ (GF := GF) 3 (by omega)).1 $$ H with ⟨H3, H⟩
    iframe
  · iintro ⟨H0, H1, H2, H3, H4⟩
    iapply (threadTok_level0 (GF := GF)).2
    iframe H0
    iapply (threadTokFrom_succ (GF := GF) 1 (by omega)).2
    iframe H1
    iapply (threadTokFrom_succ (GF := GF) 2 (by omega)).2
    iframe H2
    iapply (threadTokFrom_succ (GF := GF) 3 (by omega)).2
    iframe

/-- **The unary adapter** (Scope r5 §3.4, A4-MAJ-3): a handler proved against `grpcMethodOkMd` at
a bundle `R₁ ∗ R₂ ∗ R₃` of three leveled pools (levels 1, 2, 3; abstract `IProp`s, not known
timeless) meets the run contract: the run borrows each pool with its token's level (each loan gives
`▷ Rᵢ`), strips the joined later with the run's one credit, runs the handler, and gives the loans
back. Generic in the pools: B2/B3 instantiate it with `raftPool`, `I` and the run pool. -/
theorem grpcRunOkMd_of_pools {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep) (R₁ R₂ R₃ : IProp GF)
    (N₁ N₂ N₃ : Namespace) (γ₁ γ₂ γ₃ : GName) (HT : 4 ≤ threadBound GF) :
    □ grpcMethodOkMd mh srv ics iprop(R₁ ∗ R₂ ∗ R₃) Spec ∗
      threadPool.isThreadPoolL N₁ 1 γ₁ R₁ ∗ threadPool.isThreadPoolL N₂ 2 γ₂ R₂ ∗
      threadPool.isThreadPoolL N₃ 3 γ₃ R₃ ⊢
    grpcRunOkMd mh srv ics Spec := by
  iintro ⟨#Hm, #Hp1, #Hp2, #Hp3⟩
  iunfold grpcMethodOkMd at Hm
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨Htok, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  icases (threadTok_levels0123 (GF := GF) HT).1 $$ Htok with ⟨H0, H1, H2, H3, H4⟩
  imod threadPool.borrowL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 H1] with ⟨HR1, Hl1⟩
  · iframe; iframe #
  imod threadPool.borrowL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 H2] with ⟨HR2, Hl2⟩
  · iframe; iframe #
  imod threadPool.borrowL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 H3] with ⟨HR3, Hl3⟩
  · iframe; iframe #
  ihave HR : iprop(▷ (R₁ ∗ R₂ ∗ R₃)) $$ [HR1 HR2 HR3]
  · inext; iframe
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc HR with HR
  iapply wp_fupd
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HR Hctx Hrc Hd Hch HSpec]
  · iframe
  inext
  iintro %resp %err ⟨⟨HB1, HB2, HB3⟩, Hok, Herr, Hsrv⟩
  imod threadPool.giveBackL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 Hl1 HB1] with H1
  · iframe; iframe #
  imod threadPool.giveBackL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 Hl2 HB2] with H2
  · iframe; iframe #
  imod threadPool.giveBackL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 Hl3 HB3] with H3
  · iframe; iframe #
  imodintro
  iapply HΨ
  iframe
  iapply (threadTok_levels0123 (GF := GF) HT).2
  iframe

end adapt

/-! ## Pure facts -/

section pure
variable [GooseExts]

theorem grpc_inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: l, h, x, hx, y, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd hxy.symm (h.1 y hy')
    · exact absurd hxy (h.1 x hx')
    · exact grpc_inj_of_nodup_map f l h.2 x hx' y hy' hxy

/-- Under the joint `Nodup`, two unary entries of one name are one entry. -/
theorem grpc_regs_unique (regs sregs : List (GoString × val × GoInterface)) (name : GoString)
    (mh mh' : val) (srv srv' : GoInterface)
    (Hnd : ((regs ++ sregs).map Prod.fst).Nodup)
    (H1 : (name, mh, srv) ∈ regs) (H2 : (name, mh', srv') ∈ regs) : mh = mh' ∧ srv = srv' := by
  have Hnd' : (regs.map Prod.fst).Nodup := by
    rw [List.map_append] at Hnd; exact (List.nodup_append.mp Hnd).1
  have := grpc_inj_of_nodup_map Prod.fst regs Hnd' _ H1 _ H2 rfl
  simp only [Prod.mk.injEq, true_and] at this
  exact this

/-- Under the joint `Nodup`, two stream entries of one name are one entry. -/
theorem grpc_sregs_unique (regs sregs : List (GoString × val × GoInterface)) (name : GoString)
    (mh mh' : val) (srv srv' : GoInterface)
    (Hnd : ((regs ++ sregs).map Prod.fst).Nodup)
    (H1 : (name, mh, srv) ∈ sregs) (H2 : (name, mh', srv') ∈ sregs) : mh = mh' ∧ srv = srv' := by
  have Hnd' : (sregs.map Prod.fst).Nodup := by
    rw [List.map_append] at Hnd; exact (List.nodup_append.mp Hnd).2.1
  have := grpc_inj_of_nodup_map Prod.fst sregs Hnd' _ H1 _ H2 rfl
  simp only [Prod.mk.injEq, true_and] at this
  exact this

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

end pure

end EtcdGrove
end Perennial
