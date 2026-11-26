# `grpc.StatsHandler.wp_proof` retired: proved over the model's body (2026-11-26)

**Target.** Branch `grpc-statshandler/2026-11-26` (off `lean` `fd1d26705e`). The axiom
`grpc.StatsHandler.wp_proof` (`Proof/google_golang_org/grpc/StatsHandler.lean`) becomes a theorem over
the model's body (`models/grpc/server.go:544-554`, grpc-go v1.84.0's), translated by adding
`"StatsHandler"` to `Code/google_golang_org/grpc.toml`'s `translate` list. One trusted change makes this
possible: the post of the axiom `otelgrpc.NewServerHandler.wp_proof` gains `h ≠ interface.nil`
(approved by coordinator-E). TCB: −1 axiom, no axiom, premise or opaque added.

## The one trusted change: `NewServerHandler`'s post

`Spec/go_opentelemetry_io/contrib/instrumentation/google_golang_org/grpc/otelgrpc/NewServerHandler.lean`,
the axiom `otelgrpc.NewServerHandler.wp_proof` (`Proof/…/otelgrpc/NewServerHandler.lean`).

**Today.** The post is

```lean
  {{ (h : GoInterface), RET #h; ⌜grpcStatsHandlerOk h⌝ }}
```

**With this change.** The post is

```lean
  {{ (h : GoInterface), RET #h; ⌜h ≠ interface.nil ∧ grpcStatsHandlerOk h⌝ }}
```

The precondition (`sl ↦*□ os`) is unchanged. The spec's and the axiom's docstrings now say the handler
is never nil and why.

**Why it is true.** etcd's `server/go.mod` (the fork `upamanyus/etcd` at the pin `df6af0c36a6b`) requires
`go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc v0.71.0` (also
`examples/go.mod:52`). In v0.71.0, `NewServerHandler` is `stats_handler.go:49-92`. Every path:

| path | lines | what is returned |
|---|---|---|
| options applied | `config.go:75-87` (`newConfig`: `o.apply(c)` for each option, `return c` at `:86`) | nothing returned from `NewServerHandler` here; `c` is a fresh `&config{…}` (`:76`) |
| span kind default | `stats_handler.go:51-53` | falls through |
| the handler | `stats_handler.go:55`: `h := &serverHandler{config: c}` | `h` is a fresh pointer, never reassigned (only its fields are set, `:57`, `:74`, `:79`) |
| old-semconv meter error | `stats_handler.go:69-76`: `if err != nil { otel.Handle(err) } else { … }` | falls through |
| new-semconv meter error | `stats_handler.go:78-89`: `if err != nil { otel.Handle(err) }` | falls through |
| the only `return` | `stats_handler.go:91`: `return h` | `h` as `stats.Handler`: dynamic type `*serverHandler`, a non-nil pointer, so a non-nil interface |

`NewServerHandler` has no other `return` (checked: `return` occurs once in lines 49-92) and no `panic`.
A path on which an option's `apply`, `otel.Handle` or a meter call panics or does not return has no
post at all; that was already the axiom's claim (no panic) and is unchanged.

## The untrusted part

- `grpc.StatsHandler.spec` (`Spec/google_golang_org/grpc/StatsHandler.lean`) takes
  `⌜h ≠ interface.nil ∧ grpcStatsHandlerOk h⌝` (was `⌜grpcStatsHandlerOk h⌝`); its post
  `grpcSrvOpt v (.stats h)` is unchanged.
- Its proof: the closure's `if h == nil` (the `logger.Error` branch, whose `grpclog` logger has no spec)
  is refuted by `h ≠ nil`; the closure appends `[h]` to `statsHandlers` (`wp_slice_literal`,
  `wp_slice_append`), which is `hs ++ (if h = interface.nil then [] else [h])` of `srvOptFnOk _ (.stats h)`,
  and sets no other field, so `srvOptsSameBut` holds by `rfl`, the codec and both chains are unchanged;
  `grpcStatsHandlerOk h`, the kind's first conjunct, is the precondition's.
- The one caller, `v3rpc.Server` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Server.lean`),
  passes `NewServerHandler`'s post to `StatsHandler` as before (`exact Hh`, now the conjunction).
