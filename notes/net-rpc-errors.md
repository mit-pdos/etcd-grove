# net-rpc-errors: net/rpc's error answers (F3) and forwarded errors (F1/C1)

Branch `net-rpc-errors` off `lean` (76c00a8d81), for Upamanyu's review (#24; his guidance:
`errOk S` over exactly the server's own error answers, a trusted `OpError.Error` of Go's form in a
separate commit; C1: option (b), `callRet` admits `errAny`). Drafted for dsv-craq, whose chain node's `Read` answers
`"key doesn't exist"` (a linearized not-found), which no `errOk` over every non-empty message
allows.

## F3: `errOk` over `srvErrMsg`

`errOk S` (`Net/Proof/net/rpc/ServerDefs.lean`) now asks `S` to accept `Φ [] msg` only for
`srvErrMsg msg` (`Net/Proof/net/rpc/Errs.lean`), the messages net/rpc's server itself answers a
request with (`models/net/rpc/server.go`, `codec.go`):

| message | where |
|---|---|
| `"rpc: service/method request ill-formed: " ++ sm` | `readRequestHeader`, no dot in `ServiceMethod` |
| `"rpc: can't find service " ++ sm` | `readRequestHeader`, service not in `serviceMap` |
| `"rpc: can't find method " ++ sm` | `readRequestHeader`, method not in the service's map (the one the proof reaches) |
| `"net/rpc model: malformed value"` | the codec's `rpcErrDecode()` (`rpcgen_core.py`), the body's `Decode` (`decErr` now names it) |
| `rdErrMsg`: `"rpc: malformed frame"`, `"EOF"`, `"unexpected EOF"`, or `"read" ++ s1 ++ ": " ++ s2` | the body frame's read (`serverCodec.ReadRequestBody`): `errFrame`, `io.EOF`, `io.ErrUnexpectedEOF`, a `Read`'s `*OpError` (`net.opErrMsg "read"`) |

Go's `"rpc: server cannot decode request: …"` is never sent (`readRequestHeader` returns
`keepReading = false` with `req = nil`; the loop stops). `errCont` and the server's sticky read
error `rdErr` range over the same set (`errSrv err`: `Error()` returns a `srvErrMsg`); the
`readRequestHeader`/`readRequest` specs give `errSrv err` where they gave `errNE err`.
`srvErrMsg_ne`: every such message is non-empty, so a spec that accepted every non-empty message
still meets the new `errOk` (`withErr_errOk`, `masterSvc_errOk`, `replicaSvc_errOk`: one line each).

### Trusted text (separate commit 3d0cc4bc8b, needs the human's review)

`Net/TrustedCode/net.lean`'s `OpError.Error.impl` was an arbitrary non-empty string. It is now
`e.Op ++ s1 ++ ": " ++ s2` (`s1`, `s2` arbitrary; `"<nil>"` for a nil receiver), Go's form
(`net.go`'s `OpError.Error`: `Op`, the network and addresses, `": "`, `Err`'s message).
`examples/net/semantics`' `TestErrorsAreOpErrors` now checks `": "` after `Op` (passes).
`Net/Proof/net/Errors.lean`'s `wp_OpError_Error` gives `opErrMsg v.Op' msg`. Users adapted:
`errNE_opErr` (rpc), raxos's `errAny_resErr'` (`Dsverify/Proof/raxos/Proxy/NetAcceptLib.lean`).

## F1 (C1): done, option (b) (Upamanyu's decision, #24), no trusted text

Option (a) (`Client.Call.spec`'s non-`ServerError` errors with a fixed message, `errMsg`) would
need a trusted change: a net `*OpError` (a failed `Write`/`Read` of the client's connection) has a
model `Error()` that draws fresh `AnyString`s on each call. Upamanyu chose (b): `callRet`
(`Net/Proof/net/rpc/ServerDefs.lean`) admits a method error whose `Error()` is any string
(`models_lab.errAny`), with an answer for every message it may return:

```lean
def callRet (C : CodecSpec GF) (replyv : GoInterface) (Φ : List w8 → GoString → IProp GF)
    (e : GoInterface) : IProp GF :=
  iprop((⌜e = interface.nil⌝ ∗ C.enc replyv (fun eb => Φ eb [])) ∨
    (∃ msg : GoString, errMsg e msg ∗
      (if msg = [] then C.enc replyv (fun eb => Φ eb []) else Φ [] msg)) ∨
    (models_lab.errAny e ∗ ∀ msg : GoString,
      (if msg = [] then C.enc replyv (fun eb => Φ eb []) else Φ [] msg)))
```

Why this shape: the server calls `e.Error()` once (`service.call`, `models/net/rpc/server.go`:
`errmsg = errInter.Error()`) and passes it to `sendResponse`, which sends an error response only
for `errmsg != ""`; for `""` it sends the reply as a success (`ansRes`: `if errmsg = [] then
C.enc reply (Φ · []) else Φ [] errmsg`). `errAny`'s `Error()` may return `""` (it is any string),
so the branch must cover that case with the reply's encoding, exactly as the `errMsg` branch does;
for a non-empty message it gives `Φ [] msg`. A method forwarding such an error thus promises "some
message" (a non-empty one is an error answer, any of them). `service.call.wp_proof`
(`Net/Proof/net/rpc/service__call.lean`) proves the new branch: `errAny`'s `Error()` WP, for
each `msg` it may return, `sendResponse` with `ansRes` from the branch's `∀ msg`. Commit
e3e67f8b3d, no trusted text.

**Users.** swiftpaxos (`swift/Rcvr.lean`, `master/Rcvr.lean`) and epaxos
(`NetRpc/Bindings.lean`) produce only the `nil` branch (`ileft`): their proofs are unchanged.
quepaxa (raxos) has no net/rpc server method (no `callRet` user). dsv-craq's error branches add one
`ileft` (`iright; ileft; iexists msg`) and its `RemoveNode` uses the new branch.

**Semantic note.** `callRet` weaker (one more way to meet it) makes `methodOk`, hence `rcvrIs`,
`svcReg` and `srvServes`, weaker; epaxos's and swiftpaxos's `RpcHttpHyp.HandleHTTP_spec` (a
premise of both statements, with `srvServes` in its precondition) thus claims more: it serves
services whose methods may forward `errAny` errors. It stays true of the model (the server's own
code handles them: `service.call.wp_proof`), and no statement's text changes.

## Users adapted (no statement changed)

- Net: `Errs`, `Codec` (`decErr`), `ServerDefs`, `ServerGhost`, `Server__readRequestHeader`,
  `Server__readRequest`, `Server__ServeCodec`, their two specs; `Net/Proof/net/Errors.lean`.
- swiftpaxos: `lib/RpcHttpHyps.lean`'s `withErr_errOk`; epaxos: `NetRpc/Methods.lean`'s
  `masterSvc_errOk`, `replicaSvc_errOk`; raxos (quepaxa): `Proxy/NetAcceptLib.lean`.
- paxos, rabia and remote's counter use neither `errOk` nor the server; their proofs are unchanged.
- The kits' codec proofs (`wp_rpcErrDecode`'s `⟨rfl, by simp⟩`) are unchanged: `decErr`'s pure
  part is now `msg = "net/rpc model: malformed value"`, which `by simp` proves as it proved `≠ []`.

**Semantic note.** No `TopLevelRobustness` statement changes textually. But epaxos's and
swiftpaxos's `RpcHttpHyp.HandleHTTP_spec` (a premise of both statements) has `srvServes`, hence
`errOk`, in its precondition: with `errOk` weaker, that premise claims more (`HandleHTTP` serves
services that accept only the server's own messages). It stays true of the model, whose server
sends no other error answers, but it is a strengthening in meaning, for the reviewer's sign-off.

## Checks (C1(b), e3e67f8b3d)

Built on fk-lean1: `Net.Proof.net.rpc.service__call`, `Net.Proof.net.rpc.Results` and the six
`TopLevelRobustness` (swiftnet, rabianet, epaxosnet, quepaxanet, paxosnet, remote's counter):
4796 jobs, green. `#print axioms` of the six statements: `propext`, `Classical.choice`,
`Quot.sound` each. Here: tier-check ok (227 known, no new); gen-init `--check` (Perennial
`/shared/perennial-160fcf12a`) 271 files up to date; `proof_roots.namespace()`
`Perennial.EtcdGrove.`; `etc/goose.py`, `etc/gen-init.py` unchanged against the branch's lean base
76c00a8d81 (origin/lean has since moved on: af67426be3; not merged).
