# apierrors-fix handoff (2026-11-17)

## START HERE

Branch `apierrors-fix` (off `lean` 5fb716b5eb), worktree `/shared/etcd-grove-ctxdescs`, head: see
`git log`. Plan approved by the user, 2026-11-17, via etcd-grove-03 (`notes/soundness-1117-handoff.md`
item (2); round 2 decided by etcd-grove-03, `notes/axiom-review/apierrors-fix.md`). Stopped here for
context size; nothing past the two spec texts is implemented, nothing built (the branch does not build:
the callers of the two axioms are not updated).

Done:
- 6116eaf7bf, 32a468ca14: `Spec/k8s_io/apimachinery/pkg/api/errors/NewConflict.lean` (pre `fmt.argOk
  err`; post + `statusDetailsAt st []`), `NewInternalError.lean` (pre `∃ ei, err = ok ei ∗
  fmt.stringMethodSpec ei "Error" ∗ ⌜no Format⌝`; post + `∃ c, statusDetailsAt st [c] ∧ c.Type' =
  ""`); both elaborate. Go: `examples/premisefix/apierrorsdetails` (3 tests, pass). Review record
  `notes/axiom-review/apierrors-fix.md` (+ README row), bug record
  `notes/apierrors-new-precondition.md`, audit rows. No STATUS entry yet (add at the land stop).

Next, in order (each a form or approved; stop for anything else):
1. Five proved `New*` specs (`NewAlreadyExists`, `NewNotFound`, `NewTimeoutError`: Details set, no
   causes; `NewBadRequest`, `NewResourceExpired`: Details nil): posts + `statusDetailsAt st []`
   (stronger post of a proved spec). Proofs (`Proof/k8s_io/apimachinery/pkg/api/errors/New*.lean`,
   ~50 lines each): persist the details' points-to after `wp_auto`; causes via
   `ownSlice_nil DFrac.discard` (Perennial `Golang/Theory/Slice.lean:118`); nil Details: left disjunct.
2. `View.lean:119` `apiErrOk`'s `*StatusError` branch + `∃ cs, statusDetailsAt st cs`; `apiErrAt_ok`
   follows. `Spec/.../HasStatusCause.lean` header: replace "The details and their causes are read
   without being held ..." (fix (a): `apiErrOk` holds them read-only, so every later view agrees).
3. `errIs` (`apimodel/Defs.lean:163`) + `∃ cs, statusDetailsAt st cs`. Sites: every
   `wp_apply +noauto wp_NewX as %p ⟨%st, Hp, %Hst⟩` (62 in `apimodel/Server__*.lean`) becomes
   `⟨%st, Hp, #Hd, %Hst⟩`, and the following `unfold errIs; iexists p, st; iframe #` must also give
   the `∃ cs` (check whether `iframe` instantiates it; else a helper `errIs_intro` in Defs). Client
   files (`*Client__*.lean`, 4 mentions each) destructure and rebuild `errIs`.
4. NewConflict/NewInternalError callers: apimodel `Server__{update,remove}` (NewConflict of
   `errors.New(..)`: use `EtcdGrove.wp_New_errorString_cell` (`Proof/errors/NewVarCell.lean:142`) in
   place of `wp_New`, then `fmt.argOk` from the `*errorString` method set (no `Format`: see
   `kErrOk_errorString`, `Proof/k8s_io/apiserver/pkg/storage/etcd3/ErrOk.lean:116`));
   `Server__{get,list,create,update,remove,watch}` pass `errRead`/`errStorage`: strengthen
   `apimodelInit` (`apimodel/Base.lean:370`; no Init.lean exists, nothing proves it, so this is the
   package fact's meaning) to hold, for each, `∃ x, ↦□ mkOk (*errorString) #x ∗ fmt.stringMethodSpec
   .. "Error"`; `transformErrorToEvent` (`etcd3/transformErrorToEvent.lean:69`) from `kErrOk`
   (`Hstr`, `Hfmt`).
5. `createPods` (`RealPodControl__createPods.lean:153,272`): `apiErrOk` from `errIs` with the details.
6. The four typed-nil specs in place, pre `isPkgInit apierrors ∗ apiErrOk err`, post `□ ∀ w, apiErrAt
   err w -∗ ⌜b = match w with | .status st _ => X | .plain => false⌝` (Go `errors.go:574-737`,
   `reasonAndCodeForError`):
   - IsTooManyRequests (T): `decide (st.Reason' = "TooManyRequests") || decide (st.Code' = W32 429)`;
   - IsGone: `decide (st.Reason' = "Gone") || (!decide (st.Reason' ∈ knownReasons) && decide (st.Code' = W32 410))`;
   - IsInternalError: same with `"InternalError"`, `W32 500`;
   - IsResourceExpired: `decide (st.Reason' = "Expired")`.
   Call sites need `apiErrOk` of the error: `isExpiredError.spec` and `isWatchErrorRetriable.spec` gain
   the pre (callers `Reflector__list.lean:151`, `Reflector__watch.lean:240,375`);
   `ListPager__list.lean:79` from `pageRes` (`pager/Defs.lean:35`: its error branch + `apiErrOk err`,
   built from the apimodel's `errIs`); `Reflector__watch.lean:240` from `watchRet_cases` (keep
   `errIs`); `:375-383` from `handleAnyWatch.spec`'s post (the hypothesis: its error is `apiErrOk`).
7. Build (targeted, then full via `/shared/tmp/build-slot.sh`; `LEAN_NUM_THREADS=4` got the last full
   build under the 45G cap), `etc/tcb-report.py --check` (names unchanged; texts of NewConflict,
   NewInternalError, HasStatusCause's meaning via `apiErrOk`; 4 hypothesis texts), interfaces
   (`etc/gen-interface.py` for changed packages), gates under the full-build lock; STATUS entry;
   land stop.

Pitfalls: every lake command needs `--packages=/shared/tmp/manifest-c6b.json` (scripts: LAKE_OPTS /
LAKE_PACKAGES); `.lake/package-overrides.json` is the c6b manifest; lean-check `--max-open 2`, `--stop`
before builds.
