---
upstream: none
checked: 2026-11-24
links: []
blocks-proof: no
---

# grpc-proxy: the request/response logger panics on a payload that is not a protobuf message

With gRPC logging on in the gRPC proxy, `logFieldsFromPayload` calls `protoToJSON(p)` even when
`payload.(proto.Message)` failed, so `p` is a nil interface, and `protoToJSON`'s
`reflect.ValueOf(msg).IsNil()` panics on the zero `reflect.Value` ("reflect: call of
reflect.Value.IsNil on zero Value"). The same happens for a nil `payload` (an interceptor that
returns `nil, err` before the handler). `server/etcdmain/grpc_proxy_logger.go:61-84` at the pin
`edc800c6f`; etcd's own `etcdserver/txn/util.go:105` guards the same test with `msg == nil ||`.

**Why not an issue:** no test, found by code reading (the reflection survey of 2026-11-24,
`examples/specreq/reflect/typednil.go`, `MustPanicIsNilZeroValue`); it needs the proxy's optional
gRPC logging and a non-message payload, and `grpc-proxy` is best-effort in etcd's threat model.
The fix is `if msg == nil || reflect.ValueOf(msg).IsNil()`.

## Proof

no: `etcdmain` is not translated, and no top-level result runs the gRPC proxy.
