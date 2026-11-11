/-
**The trusted model of grpc's `(*Server).Serve`** (per-type stage B, B1a, 2026-11-11; Scope r5 §2.2,
`/shared/tmp/stageB/scope-r5.md`). Part of the trust base. B1a keeps it a standalone definition
(`model.Serve`); B1b makes it `Server.Serve.impl` (`trusted = ["Server.Serve"]` in
`Code/google_golang_org/grpc.toml`), so that the old `Server.Serve` axiom and this model never
coexist on one function.

**What it models** (grpc-go v1.84.0, `server.go`): `Serve(lis)` accepts connections on `lis` and, per
connection, runs the HTTP/2 transport, which reads each stream's headers and calls `serveStreams`'
handler, which runs `handleStream` on a fresh goroutine (`go f()`, `server.go:1107`; etcd sets no
`NumStreamWorkers`, test T4), and `handleStream` dispatches to the registered handler
(`processUnaryRPC`/`processStreamingRPC`). The model keeps exactly grpc's goroutine structure:

```go
func (s *Server) Serve(lis net.Listener) error {            // server.go:906-985
	for {
		r, st := model.acceptRun(s, lis)
		switch st {
		case runOk:   go model.runCall(s, r)                 // serveStreams' `go f()`
		case stopped: return nil                             // after Stop/GracefulStop, :971,:980
		default:      go model.serveRest(s); return r        // :982, r the listener's error;
		}                                                    // open connections keep serving
	}
}
func model.serveRest(s *Server) {
	for { r, ok := model.acceptRunConns(s); if !ok { return }; go model.runCall(s, r) }
}
func model.runCall(s *Server, r run) {                       // handleStream -> processRPC
	if r.unary {
		resp, err := r.mh(r.srv, r.ctx, r.dec, r.ui)         // wrapUnaryHandler, server.go:1284
		model.respond(s, r, resp, err)
	} else {
		var err error
		if r.si == nil { err = r.mh(r.srv, r.st) }            // :1450
		else { err = r.si(r.srv, r.st, r.info, r.mh) }        // :1457
		model.finishStream(s, r, err)
	}
}
```

`runCall` and `serveRest` are model code with bodies (proved over). The four **leaves** (`acceptRun`,
`acceptRunConns`, `respond`, `finishStream`) are **model-only names**: `google.golang.org/grpc#model.X`,
which cannot be a translated Go function's name (`#` cannot occur in a Go import path). No
`FuncUnfold` exists for them (the `axiom-tok` gate checks it), so the semantics' function table
(`functions`, abstract) gives them no body: their axioms
(`Proof/google_golang_org/grpc/model/`) are their whole semantics, and each docstring names the Go
composite it stands for. Only this model calls them.

**The run value** `r` (a model type, not Go's): a pair `(unary, payload)`, the payload of a unary call
`(mh, (srv, (ctx, (dec, ui))))` (`runUnary`), of a streaming call `(mh, (srv, (st, (info, (ctx, si)))))`
(`runStream`): the registered handler and service value, the run's context, grpc's decoder and
unary interceptor (the composed `s.opts.unaryInt`), or the server end, the `*StreamServerInfo` and
the composed stream interceptor (`s.opts.streamInt`, `nil` with no stream interceptor).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.all false

namespace Perennial

namespace google_golang_org.grpc
noncomputable section
variable [GooseExts] [GoGlobalContext]

namespace model

/-- The model-only name of `acceptRun` (see the file header). -/
@[reducible] def acceptRunName : GoString := go!"google.golang.org/grpc#model.acceptRun"
/-- The model-only name of `acceptRunConns`. -/
@[reducible] def acceptRunConnsName : GoString := go!"google.golang.org/grpc#model.acceptRunConns"
/-- The model-only name of `respond`. -/
@[reducible] def respondName : GoString := go!"google.golang.org/grpc#model.respond"
/-- The model-only name of `finishStream`. -/
@[reducible] def finishStreamName : GoString := go!"google.golang.org/grpc#model.finishStream"

/-- The model-only names, for the `axiom-tok` gate (none may have a `FuncUnfold`). -/
def names : List GoString := [acceptRunName, acceptRunConnsName, respondName, finishStreamName]

/-- `acceptRun`'s status: a call was accepted. -/
@[reducible] def runOk : w64 := W64 0
/-- `acceptRun`'s status: the server was stopped. -/
@[reducible] def stopped : w64 := W64 1
/-- `acceptRun`'s status: the listener failed. -/
@[reducible] def lisFailed : w64 := W64 2

/-- The run value of an accepted unary call (see the file header). -/
def runUnary (mh : val) (srv : GoInterface) (ci : GoInterfaceOk) (dec ui : GoFunc) : val :=
  PairV #true (PairV mh (PairV #srv (PairV #(GoInterface.ok ci) (PairV #dec #ui))))

/-- The run value of an accepted streaming call (see the file header). -/
def runStream (mh : val) (srv st : GoInterface) (info : Loc) (ci : GoInterfaceOk) (si : GoFunc) :
    val :=
  PairV #false (PairV mh (PairV #srv (PairV #st (PairV #info (PairV #(GoInterface.ok ci) #si)))))

/-- `model.runCall(s, r)` (see the file header). The run value's fields are read where they are
used (`Fst (Snd "r")` is `r.mh`, ...), as Go reads `r.mh` at the call. -/
def runCall : val :=
  glv(λ: "s" "r",
    if: Fst "r" then
      (let: "re" := (Fst (Snd "r")) (Fst (Snd (Snd "r"))) (Fst (Snd (Snd (Snd "r"))))
                      (Fst (Snd (Snd (Snd (Snd "r"))))) (Snd (Snd (Snd (Snd (Snd "r"))))) in
       FuncResolve respondName [] #() "s" "r" (Fst "re") (Snd "re"))
    else
      (let: "si" := Snd (Snd (Snd (Snd (Snd (Snd "r"))))) in
       let: "err" := (if: "si" =⟨go.GoType.FunctionType (go.signature.Signature [] false [])⟩ #func.nil
                      then (Fst (Snd "r")) (Fst (Snd (Snd "r"))) (Fst (Snd (Snd (Snd "r"))))
                      else "si" (Fst (Snd (Snd "r"))) (Fst (Snd (Snd (Snd "r"))))
                        (Fst (Snd (Snd (Snd (Snd "r"))))) (Fst (Snd "r"))) in
       FuncResolve finishStreamName [] #() "s" "r" "err"))

/-- `model.serveRest(s)`'s loop (see the file header). -/
def serveRest : val :=
  glv(rec: "loop" "s" :=
    let: "x" := FuncResolve acceptRunConnsName [] #() "s" in
    if: Snd "x" then (Fork (Val runCall "s" (Fst "x")) ;; "loop" "s") else #())

/-- `Serve`'s loop (see the file header). -/
def serveLoop : val :=
  glv(rec: "loop" "s" "lis" :=
    let: "x" := FuncResolve acceptRunName [] #() "s" "lis" in
    let: "r" := Fst "x" in
    let: "st" := Snd "x" in
    if: "st" =⟨go.uint64⟩ #runOk then (Fork (Val runCall "s" "r") ;; "loop" "s" "lis")
    else if: "st" =⟨go.uint64⟩ #stopped then "r"
    else (Fork (Val serveRest "s") ;; "r"))

/-- **`(*Server).Serve`'s model** (see the file header): the receiver, then the listener. -/
def Serve : val := glv(λ: "s" "lis", Val serveLoop "s" "lis")

end model

end
end google_golang_org.grpc

end Perennial
