# soundness-1117 handoff (2026-11-17)

## START HERE

**Plan approved by the user, 2026-11-17, via etcd-grove-03** (restructured after the blockers below):
(1) now, on `soundness-1117`, a notes-only landing: item (4)'s bug records
(`notes/ctxreaderrs-descs-unsound.md`, `hasstatuscause-later-view.md`,
`apierrors-typednil-hypotheses.md`, `incomingof-crossworld.md`; added by etcd-grove-03: `release-snapdb-held-file.md`), the Go tests
(`examples/axiomcx/{hasstatuscause,apierrorstypednil}`, own modules; `examples/axiomcx/releasesnap` in the examples module, outside the examples module and
`GO_MOD_PINS`), audit verdicts, the STATUS entry. Done; at the land stop.
(2) after it lands: branch `apierrors-fix` off `lean`: HasStatusCause fix (a) with stronger posts for
the axioms `NewConflict.wp_proof`/`NewInternalError.wp_proof` (Go tests; STOP with their old -> new
texts for an independent attack first), the four typed-nil specs in place (`apiErrOk`, answer per
view), `handleAnyWatch`'s post giving `apiErrOk` of its error, the call sites; build, tcb, interfaces,
gates, land stop.
(3) the Hctx / `ctxErrsErr` Scope (B1) goes to the incomingOf Scope agent, not this stage.


Branch `soundness-1117` (off `lean` 3cd4b72599), worktree `/shared/etcd-grove-ctxdescs`. The approved
stage (etcd-grove-03, the user's go 2026-11-17): (1) `ContextReadErrs.descs` per run, (2)
`HasStatusCause` fix (a), (3) `IsTooManyRequests.spec` fix T, (4) bug records, (5) the axiom skill's
`crossWorld` check. Counterexample Lean (`CrossWorld.lean`) stays on `axiom/ctx-descs` (4cfaf29628).

Done (one commit): the review notes from `axiom/ctx-descs` (`notes/axiom-review/ctx-descs.md`, README
row, two `notes/audit.md` rows); (5) in `.claude/skills/axiom/{SKILL,LESSONS}.md`; the Go test of the
`HasStatusCause` finding, `examples/axiomcx/hasstatuscause/` (own module; `go test` passes = Go panics).
No Lean changed. Stopped at three hard stops, below; nothing built.

### Blockers (decisions for etcd-grove-03 / the user)

B1, (1) client side. `ctxErrClient`/grpc's `ctxErrsErr` (`InvGrpc.lean:1419`, HS-5 (a), part of the
grpc model's premise `ctxOk`) has the pure conjunct `err = nil ∨ errDesc err ∉ handlerDescs`, and
`ContextError.spec`/`waitRetryBackoff.spec` posts carry it on. `ctxErrClientAllW_of` (ErrorsNewOk:254)
and `chanCtx_ok` (ChanCtx:166) prove it for `Canceled` from `descs` with only `isPkgInit context` in
hand (callers: TimeoutCtx, InvClientNewResult, the k8s compactor loops, auth examples). No per-run
source exists there: `FromError`'s wand is a post of a call not yet made; `toGRPCErrorMap_init`'s is
v3rpc's (client and k8s proofs hold no `isPkgInit v3rpc`). Any pure `errDesc (*errorString x) ∉ …`
premise has the same cross-world flaw (x = mvcc's `ErrFutureRev` location). Options: (A) make the
conjunct per run in `ctxErrsErr` (trust-model text): `err = nil ∨ ∀ e, err = ok e → ∃ m, errorMsgIs e m
∗ ⌜m ∉ handlerDescs⌝`, derive `errDesc` at the `FromError` call (the grpc invoker axiom's justification,
`ContextError.spec`, `waitRetryBackoff.spec` follow); (B) thread a per-run `v3rpc` fact to the client
(new premises: refused by the brief). Recommend (A), as its own Scope. The `DeadlineExceeded` half is
sound as a pure, location-free fact (`errDesc (mkOk deadlineExceededError.ty #zero) = …`).

B2, (2). `errIs` (daemonset apimodel `Defs.lean:163`) holds only the struct; the errors come from
`apierrors.New*`, whose posts say nothing of `Details`. Holding `statusDetailsAt` at
`RealPodControl.createPods` needs `errIs` to carry it, hence the `New*` posts: proved ones
(AlreadyExists, BadRequest, NotFound, ResourceExpired, TimeoutError: stronger posts, a form) and the
axioms `NewConflict.wp_proof`, `NewInternalError.wp_proof` (trusted text: a stop). Recommend: approve
stronger posts for those two axioms (Go: `Details: &StatusDetails{…}`, causes `[]` / one cause).

B3, (3). Call site 1 (`isWatchErrorRetriable` on the `Watch` error) can get `apiErrOk` from `errIs`
(keep it in `watchRet_cases`) but `isWatchErrorRetriable.spec` gains the precondition. Call site 2
(Reflector__watch:379) is on `handleWatch`'s error, which comes from the hypothesis
`handleAnyWatch.spec`, whose post says nothing of the error: T needs that hypothesis's post changed
(another text). New: `IsGone`, `IsInternalError`, `IsResourceExpired` specs (hypotheses of
client-go cache's `Link`) are false the same way (typed nil `*StatusError` panics; checked in Go,
`/shared/tmp/soundness-1117/typednil/t_test.go`). Recommend: one stage for all four, with the
`handleAnyWatch` post.

(4) done under the approved plan above (bug records, audit verdicts, STATUS entry).
