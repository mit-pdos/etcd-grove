# apierrors-fix handoff (2026-11-17)

## START HERE

Branch `apierrors-fix` (off `lean` 5fb716b5eb), worktree `/shared/etcd-grove-ctxdescs`. Plan approved
by the user, 2026-11-17, via etcd-grove-03 (`notes/soundness-1117-handoff.md`, item (2)): HasStatusCause
fix (a); the four typed-nil specs (`IsTooManyRequests`, `IsGone`, `IsInternalError`,
`IsResourceExpired`) in place (`apiErrOk` premise, answer per view); `handleAnyWatch`'s post gives
`apiErrOk` of its error; the call sites; build, tcb, interfaces, gates; land stop.

Done (stop 1, awaiting the independent attack of the two axiom texts):
- `Spec/k8s_io/apimachinery/pkg/api/errors/NewConflict.lean`: post + `statusDetailsAt st []`.
- `Spec/k8s_io/apimachinery/pkg/api/errors/NewInternalError.lean`: post + `∃ c, statusDetailsAt st [c] ∧
  c.Type' = ""`; NEW precondition `∃ ei, err = ok ei ∗ fmt.stringMethodSpec ei "Error"` (the old
  axiom was false: Go calls `err.Error()` directly; nil or a panicking `Error` panics).
- Go: `examples/premisefix/apierrorsdetails` (own module; gate 9b runs it), both tests pass.
- Both files elaborate (`etc/lean-check.py -a`); nothing else changed yet (callers not updated).

Next, after the go:
1. Callers of `NewInternalError`: `transformErrorToEvent` (has `kErrOk`: `stringMethodSpec e "Error"`);
   the apimodel's `Server.{get,list,create,update,remove}` and `watch` pass `errRead`/`errStorage`:
   `apimodelInit` (`apimodel/Base.lean:370`) holds only `↦□ e`; strengthen it with
   `stringMethodSpec` (from `errors.New` in the generated init, `etc/gen-init.py` SPECIAL).
2. `errIs` (`apimodel/Defs.lean:163`) + `∃ cs, statusDetailsAt st cs`; New* proved specs
   (AlreadyExists, BadRequest, NotFound, ResourceExpired, TimeoutError): stronger posts (forms).
3. `apiErrOk` (`errors/View.lean:119`) `*StatusError` branch + `statusDetailsAt st cs`; HasStatusCause
   header sentence; `createPods` holds it.
4. The four typed-nil specs; `handleAnyWatch.spec` post; `watchRet_cases` keeps `errIs`;
   `isWatchErrorRetriable.spec` gains `apiErrOk err`.

Pitfalls: full builds hit the 45G cap repeatedly; `LEAN_NUM_THREADS=4` got one through (soundness-1117).
