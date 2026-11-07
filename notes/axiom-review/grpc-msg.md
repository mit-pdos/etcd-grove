# grpc's message models as a parameter: `ProtoMsg` and `StreamMsg`

**Reviewed:** 2026-11-07, `lean` at `158829a8b9`. This is the axiom sweep's pass on the
"trusted model as a parameter" shape ([model-param-sweep](model-param-sweep.md)), after
[pbenc](pbenc.md).

**Axioms reviewed:**

- `grpc.serve` (`Proof/google_golang_org/grpc/InvGrpc.lean:961`) and
  `grpc.ClientConn.Invoke.wp_proof`, through `grpcMethodOkMd` and `grpcInvokerOk`;
- `grpc.serveStream` (`InvGrpcStream.lean:1043`) and `grpc.ClientConn.NewStream.wp_proof`, through
  `grpcStreamMethodOkR`.

**The models:**

- `ProtoMsg` (`InvGrpc.lean:78`), with fields `ty, M, send, wireLen, recv, recv_persistent, recvOwn,
  blank, own, blank_own`;
- `StreamMsg` (`InvGrpcStream.lean:101`), with fields `ty, M, cnt, send, wireLen, recv, own`.

## Verdict: refuted, both

Each structure's fields are the trusted wire model, and the caller chooses them. Nothing ties a
record to its Go type, or ties the server's `send` to the client's `recv`. So a program that
controls its own server and its own client can pick a reply model whose `recv` is `False`. A
handler that sends an empty reply then meets its spec, and the client is proved never to get the
reply, while grpc-go delivers it.

Neither refutation is a closed `False`. Each takes as hypotheses the server and connection
resources (`grpcServerAt`/`grpcStreamServerAt` from `grpc.start`, `grpcConn` from `NewClient`) and
the package's `isPkgInit`. Neither proof has a `sorry`.

### Unary calls (`ProtoMsg`)

Branch `axiom/protomsg`, commit `8d7ff9b9b4`, file
`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/protomsg/False.lean`.

- `okHandler_ok` uses no axiom. With `Rep := noRecv` (`recv := False`, `send := True`), the handler
  `return (*Rep)(nil), nil` meets `grpcMethodOkMd` for the spec "give `Φ ()`".
- `served_call_fails`:

  ```
  isPkgInit grpc ∗ grpcServerAt addr [] [(name, okHandler repTy, srvv)] ∗
    grpcConn conn [addr] [] [] ∗ ctxOk ctx cd ∗ opts ↦*□ [] ⊢
  |={⊤}=> WP conn.Invoke(ctx, name, &Req, &Rep, opts) {{ v, ⌜∃ err, v = #err ∧ err ≠ nil⌝ }}
  ```

  grpc-go returns the empty reply with a `nil` error. So `if conn.Invoke(...) == nil { panic("") }`
  is proved safe, and in Go it panics.
- `#print axioms` of `served_call_fails`: Lean's three, `grpc.serve`, `grpc.ClientConn.Invoke.wp_proof`,
  and the opaque `grpcConn`, `grpcConn_persistent`, `grpcServerAt`, `grpcServes`,
  `grpcServes_persistent`, `grpcPeerOpt` and `grpcWrotePeer`.
- A second free claim: the request's `wireLen` (the proof uses `0`) meets the attempt's premise
  `wireLen m < grpcMsgMax` on the record's own say-so.

### Streams (`StreamMsg`)

Branch `axiom/streammsg`, commit `f285e9d4aa`, file
`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/streammsg/False.lean`.

- `sendHandler_ok` uses no axiom. With `Rep := noRecvS` (`recv := False`), the handler
  `func(srv any, st grpc.ServerStream) error { return st.SendMsg((*Rep)(nil)) }` meets
  `grpcStreamMethodOkR` for the spec `fun _ _ Dn => Dn 0 ()`.
- `served_stream_recv_fails`:

  ```
  isPkgInit grpc ∗ grpcStreamServerAt addr [] [(name, sendHandler, srv)] ∗
    grpcConn conn [addr] [] [] ∗ ctxOk ctx cd ∗ desc ↦□ d ∗ opts ↦*□ [] ⊢
  |={⊤}=> WP conn.NewStream(ctx, desc, name, opts)
    {{ v, ∃ cs err, v = (cs, err) ∗ (err = nil -∗ ∃ ci, cs = ok ci ∗
         ∀ out, WP cs.RecvMsg(&out) {{ e, ∃ e', e = #e' ∧ e' ≠ nil }}) }}
  ```

  Here `d` has `ClientStreams = true`. The program
  `cs, err := conn.NewStream(ctx, &grpc.StreamDesc{ClientStreams: true}, name);
  if err == nil && cs.RecvMsg(&Rep{}) == nil { panic("") }` is proved safe. grpc-go delivers the
  empty message, so in Go it panics.
- `#print axioms`: Lean's three, `grpc.serveStream`, `grpc.ClientConn.NewStream.wp_proof`,
  `grpcConn`, `grpcConn_persistent`, `grpcStreamServerAt`, `grpcServesStream` and
  `grpcServesStream_persistent`.

## What rests on these axioms

From `.lake/tcb.json` at `158829a8b9`:

- **At least one of the four axioms:** 207 of the 4898 linked results; 59 of the 881 exported
  results, all 17 `*_safe` among them.
- **`Invoke` alone:** 178 linked, 52 exported, 17 `*_safe`.
- **`grpc.serve` alone:** 68 linked, 41 exported, 17 `*_safe`.

The list is in `notes/grpc-msg-models.md`.

These results use etcd's real message models, not bogus ones. But the axioms they rest on admit
a refutation, so the results are not trustworthy until the fix lands.

## The fix

This is the user's decision, via etcd-grove-82, 2026-11-07. The fix joins the per-type stage of
[pbenc](pbenc.md):

- grpc's message models become fixed per-type instances, the etcdserverpb request and response
  types among them, with satisfiable `recv`/`send`/`wireLen`;
- the axioms quantify only over those instances;
- the stage's gate covers `ProtoMsg` and `StreamMsg` too;
- the restated axioms are attacked before the Freeze.
