/-
`grpc.model.acceptRun(s, lis)` (per-type stage B, B1a, 2026-11-11; Scope r5 §2.2): a leaf of the trusted `Serve` model
(`TrustedCode/google_golang_org/grpcServeModel.lean`), a model-only name with no Go body of its
own. Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **acceptRun** -- the Go composite: `Serve`'s accept loop (`server.go:906-985`: `lis.Accept`,
retries on temporary errors), `handleRawConn` (:1000), the HTTP/2 transport's `HandleStreams`/
`operateHeaders` (`internal/transport/http2_server.go:646,377`), `serveStreams`' dispatch
(:1071-1110), `handleStream`'s method lookup (:1537-1675: the leading `/` cut, a path without one
malformed and answered `Unimplemented` (:1562-1566; every full name starts with `/`), the path split
at its **last** `/`, then the service's one `streams` map, in which `register` writes the unary
entries after the streams so that a unary method of a name wins, :804-816, :1562-1597), and the
request decoder `processRPC` hands the handler (:1292-1518). Under `NewServer`'s options (the
`grpcSrvOpt` kinds) there is no `UnknownServiceHandler` (:1600) and no stream wrapper (:1434-1436),
so an unregistered method is answered `Unimplemented` inside the composite (:1614, test T9) and a
registered handler is called directly or, for a stream with a stream interceptor, through it: every
registered stream descriptor sets `ClientStreams` or `ServerStreams` (`RegisterService`'s premise,
`GrpcSrvCfg`), so grpc never takes :1446's direct path for a stream when `si` is not `nil` (test
T10b shows that path for an unflagged descriptor). It returns the next call some connection of `lis` delivered
whose method `gs` has registered (`runOk`), with: the registration of the path's full name
(`∈ c.regs`/`c.sregs`: the full names are jointly distinct, `grpc.start`'s premise, so the one entry
named by the path is the handler Go's split lookup finds; an entry whose method part holds a `/` is
never dispatched to); grpc's context, decoder and chain values (the unary `ui`, the composed stream
`si`); and the client's deposit (`grpcAccepted`; `InvGrpcRun.lean`, "The pair"). It returns
`stopped` only after `Stop`/`GracefulStop` and after grpc's `s.done`, by which time every connection
is removed (`server.go:916-921, 1687-1711`), so no call is delivered afterwards, with `nil` (what
`Serve` returns then); and `lisFailed` when `lis.Accept` fails otherwise (`:982`), with the
listener's error (what `Serve` returns then), consuming the link and giving the right to keep
accepting on open connections. `lisFailed` also covers `Serve` called after `Stop`/`GracefulStop`
(`s.lis == nil`: `lis` closed, `ErrServerStopped` returned without calling `Accept`,
`server.go:910-914`); no connection is open then, so `acceptRunConns` returns `false`. `lis` is the
listener `grpc.start` consumed (the link exists only for it), whose `Accept`, `Addr` and `Close` do
not panic (`Serve` calls `lis.Addr().String()`, :929-934). -/
abbrev grpc.model.acceptRun.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface) (γ : GName) (c : GrpcSrvCfg GF),
  {{ grpcSrvLink gs lis γ ∗ grpcSrvCfg γ c ∗ ⌜grpcRepliesFit⌝ }}
    (App (App (Val (@! google_golang_org.grpc.model.acceptRunName)) (Val #gs)) (Val #lis))
  {{ (r : val) (st : w64), RET (PairV r #st);
      (⌜st = google_golang_org.grpc.model.runOk⌝ ∗ grpcSrvLink gs lis γ ∗ grpcAccepted γ c r) ∨
      ⌜st = google_golang_org.grpc.model.stopped ∧ r = #GoInterface.nil⌝ ∨
      (⌜st = google_golang_org.grpc.model.lisFailed⌝ ∗ (∃ err : GoInterface, ⌜r = #err⌝) ∗
        grpcConnsLink gs γ) }}

end spec

end EtcdGrove
end Perennial
