# net-rpc-errors: net/rpc's error answers (F3) and client errors (F1/C1)

Branch `net-rpc-errors` off `lean` (76c00a8d81), for Upamanyu's review (#24; his guidance:
`errOk S` over exactly the server's own error answers, a trusted `OpError.Error` of Go's form in a
separate commit, C1 for `Client.Call`). Drafted for dsv-craq, whose chain node's `Read` answers
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

## F1 (C1): not done, blocked on trusted text

C1 asks `Client.Call.spec`'s non-`ServerError` errors for `∃ msg, errMsg err msg ∗ ⌜msg ≠ []⌝`.
`errMsg` says `Error()` returns `msg` on every call. A net `*OpError` (a failed `Write` or
`Read` of the client's connection) cannot meet it: the model's `OpError.Error` draws fresh
`AnyString`s on each call, before and after the change above. Go's message is a function of the
fields (`TCPAddr.String`, the `Errno`'s message), but the model's `TCPAddr.String` is `AnyString`
per call too. Proving C1 needs a further trusted change: a deterministic `OpError.Error` (Go's code
over the fields, with a deterministic `TCPAddr.String`, cf. the lab's hraft decision 9(1)) or a
message fixed when the error is made. Left for the human's decision. A trusted-free route for craq:
`callRet`'s error branch also admitting `errAny e ∗ ∀ msg, …` (the server calls `Error()` once)
(notes/dsv-craq.md, F1 (a)).

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
