
## from 2a, round 1

`Grpc.addrAt ep C` is `∃ P, Http.protoAt ep (grpcOver C P)`. Two bindings of one address must agree.
2a needs a law `Http.protoAt_agree : protoAt a P ∗ protoAt a P' ⊢ ⌜P = P'⌝`, which is true since a
string's protocol is set once from its single `addrFree`.

## from 4b

1. **`httputil.GracefulClose(resp)`** (`HttpUtil.GracefulClose.spec`) takes the body's reader
   (`readerAt`), owned. The snapshot sender's timeout (`snapshot_sender.go:169`: `time.AfterFunc(...,
   GracefulClose(resp))` while the sender's goroutine runs `io.ReadAll(resp.Body)`) reads one body
   from two goroutines: the drain may steal bytes, so the sender's bytes are not a prefix of what
   the handler wrote and `readerAt`'s knowledge would be false for it. `snapshotSender.post`'s sketch
   ("`readerCloser`") does not cover it: a shared reader of trivial knowledge (a persistent "any
   goroutine may `Read` it; nothing is known of the bytes") would; GracefulClose's spec can then take
   either.
2. **The prober's `GET`s** (`Probing.proberOk`'s `AddHTTP`: a goroutine outside the program's
   threads sends `GET <url>/raft/probing` through the transport's round tripper every interval):
   requests the closed world does not account for. Their receivers are the probing handler
   (`Probing.NewHandler.spec`, which needs nothing of a request); rafthttp's protocol must allow any
   `GET` on `/raft/probing` with trivial knowledge (`Proto.hreq` true there), and `Transport.Handler`
   must route it only to the probing handler.
3. `Rafthttp.semverAt v` (provisional) is `Semver.verAt v sv` (a model `SemVer`), `semverParses s` is
   `(Semver.parse s).isSome`; `MustParse`, `New`, `Major`, `Minor`, `LessThan`, `String` have specs
   (`Spec/github_com/Masterminds/semver/v3/`); `rate.*` and `probing.*` likewise
   (`Spec/golang_org/x/time/rate/`, `Spec/github_com/xiang90/probing/`).
