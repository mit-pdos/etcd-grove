# perheap, the incoming part: the trusted texts after C1 (2026-11-18)

The per-text note of the per-heap redesign's incoming part (`notes/perheap-scope.md`, Part I, §4, §5,
§7; checkpoint C1). Tests: (a) no entailment concludes a pure fact from the incoming vocabulary; (b) what
a fresh world can build gives nothing; (c) no interpreted post concludes anything about incoming
metadata but transfers; I4' (the leaf has no interpreted producer); the P-i test (true per heap in Go).

## Deleted

| text | was | why |
|---|---|---|
| `metadata.incomingOf` (opaque) | `Proof/google_golang_org/grpc/metadata/Incoming.lean` | a pure function of a pointer (I1); the file is gone |
| `metadata.incomingOf_cancelCtx` (axiom, + `_parent_unique`) | same file | refuted (`notes/axiom-review/incomingof.md`); content proved as `metadata.ctxInMD_cancel` (`Proof/context/LibKeysChain.lean`) |
| `v3rpc.incomingOf_cancellableContext` (axiom, + `_field_unique`, `incomingOf_wrapper`) | `v3rpc/WrapperMd.lean` | refuted in meaning; content proved as `v3rpc.ctxInMD_cc` and `v3rpc.ctxInMD_wrapper` (`v3rpc/SrvCtxWeakLaws.lean`) |
| `auth.ctxTokenOf`, `auth.ctxTokenOf_md` | `auth/InvAuth.lean` | definitions over `incomingOf`; replaced by `auth.ctxToken ctx tok` and the parameter `tok` |

## Restated (trusted)

| text | old | new | tests |
|---|---|---|---|
| `metadata.FromIncomingContext.spec` (C1a) | post on `incomingOf ctx` | `∀ ctx md`, pre `ctxInMD ctx md`, post facts about `md` | attack SOUND, `/shared/tmp/perheap/c1a/attack-fic.md` |
| `traceutil.Tracer.Start.spec` (C1a) | `⌜incomingOf ctx' = incomingOf ctx⌝` | `□ ∀ md, ctxInMD ctx md -∗ ctxInMD ctx' md` | attack SOUND, `/shared/tmp/perheap/attack-tracer.md` |
| `context.WithValue.spec` (step 0 + 1b) | `⌜incomingOf c' = incomingOf parent⌝` | that conjunct dropped (1b); the transfer added in step 0 stays | weaker post; attack SOUND, `/shared/tmp/perheap/attack-accepted.md` |
| grpc model `acceptRun`/`acceptRunConns` posts, through `grpcAccepted` (`InvGrpcRun.lean`) | `▷ Spec (incomingOf ci) m Φ Ψe`; stream `□ Spec (incomingOf ci) γs Dn` | one more existential `md`: `ctxInMD ci md ∗ ▷ Spec md m Φ Ψe`; stream `ctxInMD ci md ∗ □ Spec md γs Dn` | attack SOUND (same report; true of grpc v1.84.0's `Server.Serve`, test `/shared/tmp/perheap/attack-accepted/pair/pair_test.go`) |

(a) holds: grep finds no entailment from `ctxInMD`, `incomingHeld`, `transportMDRaw` or `ctxToken` to a pure
conclusion; every pure fact about a context's metadata sits in a triple's post (`FromIncomingContext`,
`AuthInfoFromCtx`). (b): a fresh world builds `ctxInMD x none` for foreign or `Background()`-rooted chains,
nothing with `some`. (c): the interpreted laws are transfers (`_cancel`, `_timer`, `_valueCtx`, `_cc`,
`_wrapper`, `_from`). I4': `transportMDRaw` has no producer but the model's posts.

## Meaning only (text unchanged)

`context.libCtxOk` (its incoming part `incomingCtxOk := ∃ md, ctxInMD ctx md`), hence
`auth.authStore.AuthInfoFromTLS.spec`, `auth.NewAuthStore.spec`'s `isReqAuth`, `grpcRunCtx`,
`srvRawStreamIs`, `client.WithRequireLeader.spec`, `context.WithTimeoutBackgroundMd.spec` (Scope §7, the
last paragraph). `AuthInfoFromTLS` still rests on `peer.transportPeer` (peer part: Part II).

## Remark (outside the model's scope)

The attack notes that `transportMDRaw`'s docstring extends to grpc's `ServeHTTP` transport, where the
pair equation `grpcAttemptMd` likely fails for `cookie` headers (net/http merges them). The model covers
only `Server.Serve`, so nothing is refuted; if `ServeHTTP` is ever modeled, `grpcAttemptMd` must handle
`cookie`.
