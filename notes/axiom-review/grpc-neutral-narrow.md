# Review: grpc's `.neutral` server option narrowed to a whitelist (2026-11-26)

**Target.** Branch `grpc-neutral-narrow/2026-11-26` (off `lean` `820a287c3a`). The definition
`srvOptFnOk` (`Proof/google_golang_org/grpc/InvGrpcServer.lean`), which says what the closure of a
grpc server option of each kind (`SrvOptKind`) does to `serverOptions`, and through `grpcSrvOpt` the
axiom `grpc.NewServer.wp_proof` (`Spec/google_golang_org/grpc/NewServer.lean`), which takes options of
any kinds and promises a server being built (`grpcSrvNew`) whose chains are the options'. Trust-shrinking:
the definition is narrowed, no axiom, opaque or premise is added, and no statement's text changes.

## What was wrong

`srvOptFnOk f .neutral` asked only that the closure keep `chainUnaryInts`, `chainStreamInts` and
`statsHandlers`; every other field of `serverOptions` was free ("a size limit, the stream limit, the
codec, the keepalive policy"). grpc's translation is the model's (`models/grpc`), with bodies, so a
program can prove facts about grpc's own option constructors from their bodies. The model's

```go
func UnaryInterceptor(i UnaryServerInterceptor) ServerOption {
	return newFuncServerOption(func(o *serverOptions) {
		if o.unaryInt != nil { panic(...) }
		o.unaryInt = i
	})
}
```

sets only `unaryInt`, so its closure meets `srvOptFnOk _ .neutral` (and `.chainUnary []`), and the
program gets `grpcSrvOpt v .neutral`. `NewServer`'s axiom then gives `grpcSrvNew gs [] [] [] [] []`:
a server whose chain is empty, which `Serve`'s axiom runs as `grpcServes` says, the handler directly.
Real grpc-go (and the model's `NewServer`, `chainUnaryServerInterceptors`, `server.go:1092-1108`)
prepends `i` to the chain, so `i` runs in front of every handler: an `i` that panics, or that never
calls the handler, refutes `Serve`'s promise over the model, and a closed program's adequacy gives
`False` (inferred from the definitions; not built as a Go test and Lean proof). The same holds of every
other field the server reads where a handler, its run context or decoding depends on it:

| field | option | effect, not represented by any kind |
|---|---|---|
| `unaryInt` | `UnaryInterceptor` | an interceptor in front of every unary handler |
| `streamInt` | `StreamInterceptor` | an interceptor in front of every stream handler |
| `creds` | `Creds` | the model panics NotModelled on non-insecure credentials (`NewServer`) |
| `cp`, `dc` | `RPCCompressor`, `RPCDecompressor` | the model panics NotModelled (`NewServer`) |
| `unknownStreamDesc` | `UnknownServiceHandler` | an unregistered method runs a handler, not `Unimplemented` |
| `streamWrapper` | `xdsFilterWrapperOption` (internal) | wraps every stream before its handler |
| `codec` | `ForceServerCodec`, `ForceServerCodecV2`, `CustomCodec` | a non-protobuf codec decodes requests otherwise than the wire models (`ProtoMsg`) say |

## The fix

`srvOptFnOk`'s every kind now also requires `srvOptsSameBut so so'`: `so'` equals `so` with only the
whitelisted fields (and the codec, the two chains and the stats handlers, which each kind states itself)
replaced. Written as `so' = { so with f := so'.f, … }` over the whitelist, so a field grpc adds later is
fixed by default. The whitelist, each checked against `NewServer`'s and `Serve`'s claims (no handler, run
context or decoding depends on it; at most a call fails, waits, or loses its reply, an error the client's
specs allow):

| field | why it changes no handler, run context or decoding |
|---|---|
| `maxConcurrentStreams` | streams over the limit wait or are refused before dispatch (a refused, undispatched stream is the one transparent retry `Serve`'s argument allows) |
| `maxReceiveMessageSize` | a request over it fails in `dec`/`RecvMsg` with a `status` error (`statusErrOk`), which both run contracts allow |
| `maxSendMessageSize` | a reply over it is not sent: a `status` error for the client, no handler's description |
| `keepaliveParams`, `keepalivePolicy` | connections are pinged or closed (GOAWAY): calls fail, as on any connection loss |
| `initialWindowSize`, `initialConnWindowSize`, `staticWindowSize` | HTTP/2 flow control: timing only |
| `writeBufferSize`, `readBufferSize`, `sharedWriteBuffer` | the transport's buffering: timing only |
| `connectionTimeout` | the handshake deadline: a connection fails before any call |
| `maxHeaderListSize`, `headerTableSize` | a call with headers over the limit is refused before dispatch |
| `numServerWorkers` | workers run the same `handleStream`, falling back to a new goroutine when busy (the model has no workers, "invisible") |
| `waitForHandlers` | read only by `Stop`/`GracefulStop`, which no spec covers |

The codec: `.neutral` allows `srvCodecOk so so'`, the codec unchanged or
`interface.mkOk codecV0Bridge.ty #(codecV0Bridge.mk c)` for a `c` with `grpcProtoCodec c`, exactly what
`CustomCodec(c)` stores (`o.codec = newCodecV0Bridge(c)`, `models/grpc/codec.go`: a `codecV0Bridge` value
whose `Marshal`/`Unmarshal` are `c`'s). Chosen over a kind of its own for `CustomCodec` because it keeps
`CustomCodec`'s spec and `NewServer`'s text unchanged, and over "the codec unchanged" because etcd's
`v3rpc.Server` needs `CustomCodec(&codec{})` neutral. `ForceServerCodec(c)` stores a `codecV1Bridge` and
`ForceServerCodecV2(c)` stores `c` itself: neither matches, so neither is neutral. The other kinds keep the
codec.

## Why `NewServer`'s axiom is now true

An option of a kind leaves `creds`, `cp`, `dc`, `unaryInt`, `streamInt`, `unknownStreamDesc` and
`streamWrapper` at `defaultServerOptions`' values (nil), the codec nil or a protobuf codec's bridge, and
changes the chains and stats handlers only as its kind says. So the model's `NewServer` panics on none
(credentials and compressors nil), composes the chain from `chainUnaryInts`/`chainStreamInts` alone
(`unaryInt`/`streamInt` nil: nothing prepended), answers an unregistered method `Unimplemented`, wraps no
stream, and decodes with protobuf's codec: what `grpcSrvNew gs (srvOptsUnary ks) (srvOptsStream ks) …`
and `Serve`'s axiom over it say. The whitelisted fields change timing and failure only.

## The option specs

- Proved over the model's bodies, re-proved (the pure post gains `srvOptsSameBut so so'`, by `rfl` on the
  closure's single field store, and `srvCodecOk`'s first disjunct): `MaxConcurrentStreams`,
  `MaxRecvMsgSize`, `MaxSendMsgSize`, `KeepaliveEnforcementPolicy` (`.neutral`), `ChainUnaryInterceptor`,
  `ChainStreamInterceptor` (the chain kinds, codec unchanged). Their statements are unchanged.
- Axioms whose post claims a kind, re-checked against the model's bodies, text unchanged:
  `grpc.CustomCodec.wp_proof` (`.neutral`: the body sets only `codec`, to `newCodecV0Bridge(c)`, the second
  disjunct of `srvCodecOk` under its premise `grpcProtoCodec c`; docstring says so) and
  `grpc.StatsHandler.wp_proof` (`.stats h`: the body appends `h` to `statsHandlers`, or nothing for a nil
  `h`, and sets no other field).
- `v3rpc.Server`'s spec takes the caller's options as `.neutral` (`grpcSrvOpt v .neutral`); its proof uses
  `.neutral` abstractly and is unchanged.
