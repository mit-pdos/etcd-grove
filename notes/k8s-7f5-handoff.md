# k8s 7f-5 handoff (2026-11-13; branch `k8s-7f5`, worktree `/shared/etcd-grove-k8s7f`)

**Read first:** `notes/k8s-7f5-scope.md` (this stage's Scope, for etcd-grove-81's review),
`notes/k8s-7f-scope.md` (the parent plan; §2, §4, §5.3), `notes/k8s-7f4-freeze.md` (the context-key
refutations T-h..T-k: the lesson for every trusted context text), `/shared/tmp/coord-81/common-rules.md`,
the worktree's untracked `questions.md` (decisions; never re-add it tracked).

## Done
- Branch `k8s-7f5` off lean `222c3fcff7` (k8s-7f4 merged and deleted).
- The Scope (`notes/k8s-7f5-scope.md`), reviewed: 81 decided Q1-Q7 as recommended (§8 there, questions.md).
- S0 (enumeration, Go evidence `examples/premisefix/watcherctx`, Goose dry run, the driver's
  `watchList()`, the no-other-mutator check) and S1 (T5-b in `CtxKeys.lean`, T5-c in `Gate.lean` with
  `watchList`'s spec/proof and the `Main*` proofs; T5-d text only): `notes/k8s-7f5-freeze.md`.

## State
- Dependencies (Scope §2): 7f-3 **missing** (not started); 7c-3 and 7e-1 **landed** (7c-3 folded into
  7e-1, 7e Freeze `8809f94d74`); sweep repairs B5 **landed with `featureOff` only** (`featureOn` is
  this stage's T5-c); 7f-0 partial (records only; the rest goes with 7f-6, Q7).
- No Lean edited. Nothing built on this branch.

## For 7f-5a: klog's `printf` boundary is restricted (klog-args-fix, 2026-11-14)

`klog.Errorf.wp_proof` and `klog.Verbose.Infof.wp_proof` now take the arguments' slice and
`klog.argsOk f xs` (`Spec/k8s_io/klog/v2/Args.lean`), given back: Go refuted "any arguments"
(`notes/klog-args-fix.md`). The watcher's `klog.Warningf("watch chan error: %v", err)` boundary takes
the same form (`notes/klog-args-fix.md`, "For 7f-5a: the restricted `Warningf`"): one error argument
whose `Error()` returns (`fmt.argOk err`), discharged by `klog_args_intro`, `klog.argOkAt_of_argOk`,
`itrivial`. A width or precision of more than 7 digits no longer parses (`fmt.maxNumDigits`).

## START HERE (2026-11-16, nineteenth 7f-5 agent): step 5 DONE (startWatching proved over a PENDING client spec); land-stop checks

- **watchChan.startWatching PROVED** (`Proof/.../etcd3/watchChan__startWatching.lean`, no sorry, lake-built), over the
  callee hypotheses incl. a **PENDING** `clientWatchCE.spec` (defined in that file): E2's remaining gap, the client
  watch's close error as `clientErr` + `errCellOk` (questions.md, OPEN for 81). Not linked (step 7).
- Forms (questions.md, nineteenth agent): startWatching spec + `threadTok`, `bmReq → forceInit`, the resource prefix's
  length; stronger posts: parseEvent (errorString), GetCurrentResourceVersion (`errCellOk`), NewTooLarge (`Failure`),
  `WatchResponse.Err` (`errCellOk` transfer); new `WithPrevKV`, `metrics.RecordEtcdEvent/Bookmark` specs (axioms at
  step 7, T5-f approved), `OptsOwn.lean`.
- **errors.AsLeaf derived** from AsLeafTy (81's decision): premise for a non-interface target, the two rafthttp callers
  discharge it; `etc/link-lean-first-server.txt` (`errors_AsLeaf: errors_AsLeafTy`), server `Link.lean` regenerated.
- lean merged (4d6437b44a). Land-stop checks all green (full build, tcb + collections updated: AsLeaf out, AsLeafTy in,
  k8s gains fmt.ErrorfPlain; links, api, interfaces, bounds, mode); steps 1-5 landed on 81's go.
- **OPEN, next unit (81, 2026-11-16): `clientWatchCE`** (unlinked hypothesis of startWatching's proof): close it before
  step 7. First check what grpc's stream `Recv` trust-boundary texts give of their errors; any trusted text goes to 81.
  Then strengthen the client watch's element (ledger entry) with `clientErr`/`errCellOk` of the close error and prove it
  through `closeErrPub`, WatchRun, `watchGRPCStream.run`/`serveSubstream`. Step 6 after 81's word.
- Proof pitfalls met: `pkill -f` on a pattern kills your own shell; `word` errors with an unused `[HasExt idIssueExt]`
  section variable (removed); `iunfold kvAu` in the context breaks `wp_for`'s simp (unfold only in the side goal);
  `emp` is a Bool variable of these specs (write `iprop(emp)` for BI emp in terms).

## START HERE (2026-11-15, eighteenth 7f-5 agent, final): steps 1-2 DONE (syncPaginated proved, ErrOk), step 3 (startWatching) next

- **Decided by 81 this round** (questions.md): previous forms accepted; store.Watch premise `uint.Z n < 2^63 - 1`
  (ledger, Draft §3, `Draft7f5a.lean`: done); `Pos.Countable KRaw` at step 6; **errors.AsLeafTy APPROVED**: now an
  axiom (`Proof/errors/AsLeafTy.lean`; header with the reviewer's wording; Go test
  `examples/premisefix/watcherctx/asleafty_test.go`, passes under -race). `errors.AsLeaf` is KEPT (rafthttp's two proofs
  use it; deriving it from AsLeafTy needs an extra premise (underlying types) on its statement: for 81 at the land stop).
- **E1 applied** (`ee8f7c876c`): `grpcStatusRO`/`grpcStatusROP` and `statusCode` (moved from FromError's spec) in
  `Proof/google_golang_org/grpc/status/StatusRO.lean`; `grpcErrMethodsOk`'s GRPCStatus conjunct gives
  `grpcStatusRO s (statusCode e)`; new axiom `status.Status.Code.wp_proof` (`Spec/.../grpc/status/Status__Code.lean`);
  FromError/Code docstrings updated; `notes/axiom-review/grpc-status-immutability.md` "Resolved".
- **ErrOk.lean done**: `kErrOk_intro` (generic, over AsLeafTy), `kErrOk_errorString`, `kErrOk_client`
  (`kClientErr err ⊢ kErrOk err`), `kErrOk_statusError` (`StatusError.Error` translated with its body:
  `Code/k8s_io/apimachinery/pkg/api/errors.toml`; `etc/goose.py --project k8s-apiserver --perennial /shared/perennial-e9e6351d9`).
- `listErrF`'s first arm is `kClientErr`; `kWcProd`'s pure conjunct now `kp ≠ []` (step 6: `prepareKeyM_ne_nil`).
- **etcd3's package fact** (`registryFact`) also holds `globalAddr defaultWatcherMaxLimit ↦□ W64 10000`
  (`etc/gen-init.py` SPECIAL, Init regenerated, StartCompactorPerEndpoint adapted).
- **watchChan.syncPaginated PROVED** (`c837473662`, no sorry): `SyncPages.lean` (pure: `syncGs`, `srvRangeOk_sync`,
  `srvRangeOk_key0`, `syncNext`, `queue_prefix`, ...), `wp_syncGet` (one page through `client_range_any`),
  `optsOwn`/`wp_optsOwn_append`, `syncGsOf`. Callee hypotheses: AsLeafTy, EtcdError.Code, Status.Code, WithRev/Limit/Range,
  GetPrefixRangeEnd, RecordEtcdRequest, ErrorfPlain, interpretListError, parseKV, queueEvent. Not yet linked (step 7).
- **Next:** step 3, startWatching (template compactor__runWatchLoop; the watch phase `kProdAt`; errors via kErrOk_*;
  `kProdExited` before each sendError and close). Then the land-stop checks (81's list).
- **Rebuild cost:** cache `Base.lean` changed: everything importing it rebuilds (~15 min for ErrOk's imports).
  Targeted build of the changed definitions' users: `/shared/tmp/k8s7f5a-p4/build-step5b.log`.

## START HERE (2026-11-15, seventeenth 7f-5 agent): step 5 statements written, sync proved; syncPaginated/startWatching proofs next

- **Build:** `--packages=/shared/tmp/manifest-e9e.json` (lean-check: `LAKE_OPTS=...`); restart the lean-check server
  (`--stop`) when it sits at "line 1".
- **Design fix (form, in questions.md):** a `queueEvent` that takes the element's resource before the send cannot
  serve `kInElem`: a dropped event's index would already be in `γ.raws`. `queueEvent` now takes the commit form
  (`S ∧ (£1∗£1∗£1 -∗ ∀ Φ, ▷ (Q -∗ Φ) -∗ sendAu γch e Φ)`, post `Q ∨ (□ cdw.PDone ∗ S)`); `sendError` likewise
  (`S ∧ commit`, post `Q ∨ S`: 81's "keep the alive token outside the wand"). `sendEvent` still returns the commit
  (step 6: give it the same form).
- **Design fix (form):** `kErrOk`'s comparison conjunct was "with any value", unprovable for a pointer error (no step
  for `GoEquals` on a non-`Loc`); now pure: of type `*errorString`, a `Loc`; of type `EtcdError`, an `EtcdError`
  (the two comparands, `context.Canceled` and `rpctypes.ErrCompacted`); `wp_kErrOk_eq_ptr`/`_etcd` replace
  `wp_kErrOk_eq` (isCancelError, interpretWatchError re-proved).
- **New `WatchProd.lean`:** `kIncTok` (SPSC producer half + half of `γ.raws`' authority), `kInc_commit`,
  `kProdSt γ cd I` (the producer's raws a subsequence of `I`, all of it unless cancelled), `kCdw`, `kProd_drop`,
  `kProd_queue` (the conjunction `queueEvent` takes and the state at `I ++ [r]` after either outcome), pure `kProdAt`
  (watch phase: `I` = initial part ++ a `KRawSeg` from `st` to the cursor `c`; `kProdAt_ok/_step/_hist/_start`,
  `kInit_ok`, `kRawStreamSub_of_ok`), `kInitRaws`, `kWcProd` (the fields/channels bundle), `kStartPre`.
- **New `ErrOk.lean`:** `kErrOk_errorString` (over `errors.AsLeaf`). Still to write: `kErrOk` of a client error
  (`clientErr ∗ statusErrOk`: `*status.Error` needs E1 (`grpcStatusRO`, `(*Status).Code`); all non-`*errorString`
  types need `errors.AsLeafTy`, DRAFT trusted text `Spec/errors/AsLeafTy.lean`, NOT approved: take it as a
  hypothesis) and of a `*StatusError` with a `Failure` status (E5's `NewResourceExpired`, E6): its `Error()` is
  names-only (no spec, no body: translate `StatusError.Error` with its body in
  `Code/k8s_io/apimachinery/pkg/api/errors.toml`, as `StatusError.Status` was, then `etc/goose.py`; no trusted text).
- Targeted build after these changes green: `/shared/tmp/k8s7f5a-p4/build-step5a.log` (7488 jobs, the WatchDefs
  importers' leaves and `watchChan__sync`).
- **Specs:** `watchChan__syncPaginated`, `watchChan__sync` (proved over syncPaginated), `watchChan__startWatching`.
- **Next, in order:** (1) syncPaginated's proof (template: `kubernetes/Client__List.lean`'s `client_range_any`;
  pages via `ListPages.lean`'s `fromL_kp`/`fromL_next`; each kv via `parseKV` + `ipersist` + `kProd_queue` with
  `kInit_ok`; first page fires `Q lbf` (re-armed reads for later pages, `kvSameHist_at` to the first page's store);
  errors: `interpretListError` (E5; strengthen `listErrF`'s first arm to `kClientErr` so that `kErrOk` follows, a
  stronger post) and `fmt.ErrorfPlain` → `kErrOk_errorString`); (2) the kErrOk lemmas above; (3) startWatching
  (the client watch loop: `compactor__runWatchLoop.lean` is the receive-loop template; `kProdAt` along responses,
  the later of two states by `kvSameHist`; errors E2/E4/E6 → kErrOk; `kProdExited` set before each `sendError`
  and before closing `watchClosedCh`, `wp_broadcast_chan_close`). STOP before step 6.
- **Open for 81 (questions.md):** (a) `errors.AsLeafTy` (trusted, generalizes AsLeaf); (b) the Draft's `uint.Z n <
  2^63` premise of `store.Watch` lets `WithRev(n + 1)` overflow for a watch without initial events at `n = 2^63-1`
  (the client `Watch` spec needs `1 ≤ rev`): `kStartPre` asks `uint.Z r0 + 1 < 2^63` there; the Draft premise
  needs `< 2^63 - 1`; (c) `Pos.Countable KRaw` has no instance (a binder of every spec; step 6 derives one).

## START HERE (2026-11-15, sixteenth 7f-5 agent, final): E2, E4, E5 done; lean merged (9e678b61e7, e9e pin); step 5 next

- **Build:** `--packages=/shared/tmp/manifest-e9e.json`; `.lake/packages` links only iris, batteries, Qq. A full build
  at the e9e pin (before E4's final form and E5's proof) was green but for the then-new handleCompacted spec
  (`/shared/tmp/k8s7f5a-p3/full-e9e.log`); targeted build after E4/E5: `/shared/tmp/k8s7f5a-p3/build-e4e5.log`.
- **E4 final:** `GetCurrentResourceVersion`'s error arm `⌜err ≠ nil⌝ ∗ ((⌜clientErr err⌝ ∗ statusErrOk err) ∨ ∃ x,
  ⌜err = mkOk (*errors.errorString) #x⌝ ∗ fmt.stringMethodSpec … "Error")`, from the fixed `fmt.ErrorfPlain`
  (callee `fmt_ErrorfPlain`, a trust-boundary entry in `etc/link-lean-first-k8s-etcd3.txt`; the k8s etcd3 tcb
  collection now reaches the `fmt.ErrorfPlain.wp_proof` axiom: run `etc/tcb-report.py --check` and the collection
  checks at the land stop).
- **E5 done:** `interpretListError` over any `paging` (premise `paging = true → encOkL ck kp`, post `listErrF`),
  `handleCompactedErrorForPaging` proved (`wp_apply` does the nested `ListMeta.Continue` store itself).
- **Next:** step 5 (`sync`/`syncPaginated`, `startWatching`) with `-- pending E1` (E1's fixed text, §11.2, approved:
  apply it with step 5), `kErrOk` of each error sent; T5-f pointer form approved (step 7). STOP before step 6
  (Perennial e9e has `wp_WithCancel_ctx`; `spsc_send_commit_inv` must keep `kResAlive` outside the wand).
- Pitfalls: the lean-check server sometimes sits at "line 1" after imports change though they build: `--stop`
  and re-run; never `pkill -f` a pattern in your own command line.

## START HERE (2026-11-15, sixteenth 7f-5 agent, latest): E4 done, E5 WIP; lean merged at the e9e pin

- **Pin:** lean merged (`cbae1bea7d`, lean 73cffb21d3, Perennial e9e6351d9). Use
  `--packages=/shared/tmp/manifest-e9e.json` everywhere; `.lake/packages` is now a real directory linking only
  iris, batteries, Qq. Full build after the merge: `/shared/tmp/k8s7f5a-p3/full-e9e.log`.
- **E4 done** (`GetCurrentResourceVersion`: error arm `⌜err ≠ nil⌝ ∗ ((⌜clientErr err⌝ ∗ statusErrOk err) ∨
  kFmtErr err)`; the spec imports `WatchDefs`). To strengthen to the no-wrap `*errorString` once the ErrorfPlain
  fix (from /shared/etcd-grove-auth3) lands on lean: merge lean again on 81's word.
- **E5 WIP** (`782d45245e`): `interpretListError.spec` over any `paging` (premise `paging = true → encOkL ck kp`,
  post `listErrF`, new in `ListDefs` with `listErrF_listErr`); new `handleCompactedErrorForPaging` Spec/Proof
  (proof ends in `sorry` after `NewResourceExpired`: the nested store `statusError.ErrStatus.ListMeta.Continue =
  newToken` -- try `wp_auto`'s field-store instances, else `iStructNamed` three levels and recombine with
  `typedPointsto_split`'s reverse, then `ipersist`); link list updated (`handleCompactedErrorForPaging:
  EncodeContinue NewResourceExpired`); `Link.lean` of k8s-etcd3 NOT yet regenerated
  (`etc/gen-link.py --k8s-etcd3`). Nothing of E5 checked yet.
- Then step 5 (with `-- pending E1`/`-- pending E3`), apply E1 with it; STOP before step 6 (Perennial now has
  `wp_WithCancel_ctx` for it).

## START HERE (2026-11-15, sixteenth 7f-5 agent, later): ghost steps done, E2 done; STOPPED on a soundness finding (fmt.ErrorfPlain)

- 81's decisions after the axiom review (questions.md): E3 and T5-f's pointer form approved (add as trusted text
  when step 5 needs them, tcb diff exactly that); E1 approved with fixes 1-5, applied to §11.2 (`be44d3c8e9`);
  not yet in Lean. Trusted-text edits land with the stage, each with its Go test, tcb diff at the land stop.
- **Done:** `kResInv_step` (the shared core), `kResInv_send_acc`, `kResInv_filter`, `kProcExited_refute`,
  `kvSameHist_refl` (`WatchRes.lean`, lean-checked); **E2** (`WatchResponse.Err.spec` post gains `statusErrOk err`
  and `⌜AsTarget EtcdError → (closeErr ≠ nil → clientErr closeErr) → clientErr err⌝`; new callee
  `rpctypes.EtcdError.Error` added to the four link lists and the four `Link.lean` regenerated; targeted build of
  the callers green after two pattern fixes (`Cache__watchEvents`, `compactor__fromWatchResponse`):
  `/shared/tmp/k8s7f5a-p3/build-e2b.log`, 8290 jobs). No `etc/api` list holds the spec (etcdstart's interface
  names it only); run `gen-interface --check` of every list after the next full build.
- **Soundness finding (STOP):** `fmt.ErrorfPlain.wp_proof`'s premise `¬ "%w" infix` admits `%+w`, `%-5w`, ...
  which Go wraps: `notes/axiom-review/errorfplain.md`, Go counterexample `examples/axiomcx/errorfplain`. Latent
  (its two rafthttp callers use no `w` verb). Proposed fix: E3's premise.
- **Next, in order:** E4 (`GetCurrentResourceVersion`: error arm `⌜err ≠ nil⌝ ∗ ((⌜clientErr err⌝ ∗ statusErrOk
  err) ∨ E3 form)`; needs E3 in Lean, which changes `fmt.Errorf.spec`'s post: 67 files use it, so prefer
  adding E3 as its own conjunct that callers' patterns absorb, or as a separate derived spec), E5, step 5.
- Pitfall: the abort branch of `sendEvent`/`sendError` returns the `Hsend` wand, which holds `kResAlive` (`T`)
  inside `spsc_send_commit_inv`: step 6 (`run`'s `Wait`) needs `kResAlive` back from an aborted send; revisit
  `spsc_send_commit_inv` then (keep `T` outside the wand, e.g. an Iris `∧`).

## START HERE (2026-11-15, sixteenth 7f-5 agent): Go evidence for E1, E3 and T5-f-ptr written; review package with 81

81's decisions (questions.md, sixteenth agent): previous forms accepted; `alive` stays a parameter until step 6;
Go evidence for E1/E3 first, then 81 has the package reviewed (not applied until 81 says so). The user (via 81)
added **T5-f over the pointer receiver** (`StringPtr` form as an axiom in place of waiting for the goose change),
drafted in `notes/k8s-7f5a-draft.md` §11.5, same review package, not an axiom yet.

- **Done:** `examples/premisefix/grpcstatusro/` (E1: static no-write scan of etcd's and k8s' closures, producers,
  ErrGRPC* initializers, invoker/stream errors under `-race`, the negative), `examples/premisefix/errorfwrap/`
  (E3: watcher formats, `w` forms, a Go port of `fmtDirectivesAux` + 200000-format differential test),
  `examples/premisefix/eventtypestr/` (T5-f-ptr). All pass (`-race`, go1.27.3, 32G cap; logs
  `/shared/tmp/k8s7f5a-p3/`). §11.2, §11.3 carry the evidence; §11.5 the T5-f-ptr draft.
- Run: `cd examples && GOWORK=off GOTOOLCHAIN=go1.27.3 go test -race -count=1 ./premisefix/{grpcstatusro,errorfwrap,eventtypestr}/`
  under `systemd-run --scope -q -p MemoryMax=32G` (TestNoStatusWriteK8s runs `go list` in `../watcherctx`).
- **Next, in order (unchanged):** `kResInv_send_acc`, `kResInv_filter` (fifteenth agent's (1) below), E2/E4/E5
  spec changes, step 5 with `-- pending E1`/`-- pending E3` hypotheses. STOP before step 6.

## START HERE (2026-11-15, fifteenth 7f-5 agent): send lemma, kResChan, Error step done; processor step next

81's decisions (questions.md, fifteenth agent): E1-E6 reviewed (`notes/k8s-7f5a-draft.md` §11.1-11.4); E1 refuted
as written and folded, with the latent `*Status` immutability assumption of `status.FromError`/`status.Code`
(`notes/axiom-review/grpc-status-immutability.md`, docstring pointers on both axioms, approved), into the E1
trusted-text package; E1 package and E3 DRAFTED in §11.2-11.3 for 81's review (not applied); E2, E4, E5 are
proved-spec changes, ledger entries written (2026-11-15 E2/E4/E5), specs NOT yet changed; E6 reachable: use the
existing `NewTooLargeResourceVersionError` spec.

- **Done** (`Proof/k8s_io/apiserver/pkg/storage/etcd3/WatchRes.lean`, lean-checked in full, no `sorry`):
  `spsc_send_au_inv` (local copy of `spsc_send_au` over `inv nroot (spscInv γ P R ∗ X)`; accessor
  `Hacc : T -∗ X ==∗ ∃ sent, spscProducer γ sent ∗ P sent.length v ∗ (spscProducer γ (sent ++ [v]) ==∗ X ∗ T ∗ Q)`,
  closed states refuted by `Hnc : □ (T -∗ X -∗ ∃ sent, spscProducer γ sent)`), `spsc_send_commit_inv` (the
  `Hsend` form of sendEvent/sendError, with `T ∗ Q`); `kResAlive alive q` / `kResClosed alive` (a new ghost
  name `alive`: each sending goroutine holds a fraction of `false`; `run` gathers them after `Wait()`, sets `true`
  and swaps `kResInv` for `kResClosed` to take the token for `close`), `kResChan … procd alive ch` (`isChan ∗ inv
  nroot (spscInv γ.res (kResElem …) True ∗ (kResInv … ∨ kResClosed alive))`), `kResChan_isSpsc` (`inv_split_l`),
  `kResChan_nc`; **the Error step** `kResInv_err_acc` (the accessor for any Error event with `statusFailureAt`);
  pure: `kEvs_types`, `kNonErr_append_err`/`_ev`, **`kRes_step_pure`** (the processor's step at the later of
  `kResInv`'s σ and the element's σr: new equation, element facts carried; `oe = none` is the filtered case);
  `monoList_lb_idx_all`, `monoList_idx_prefix`, `monoList_idx_lb_snoc` (kResInv's `raws` lb and the element's
  indices, same length via `procd`: `raws = raws'` and lb `raws' ++ [r]`).
- **Next, in order:** (1) the processor's Iris step `kResInv_send_acc` (and `kResInv_filter`, a plain ghost update
  without a send): inputs the processor's `dghostVar procd ½ n`, the element (`kInElem` at `n`: idx bigsep,
  `□ Q lb σr`, `□ Q lb0 σ0`, `kStartOk`, `kRawStreamSub`, `kRawStreamOk ∨ kCancelled ∨ kProcExited`), its
  `dghostVar γ.procEx (own q') false` (refutes `kProcExited`), `wevAt v e` with `kRawToEv σr r = some e`, and the
  `Q` history premise (`Q lb σ ∗ Q lb' σ' ⊢ kvSameHist`); steps: `monoList_idx_lb_snoc` (raws = raws'),
  `kRes_step_pure`, pick `□ Q` of the chosen σ', update `procd` halves to `n+1`, `monoListAuthOwn_update_app [e]`,
  build `kResElem` as in `kResInv_err_acc`. (2) E2, E4, E5 spec changes (ledger done). (3) step 5 with
  `-- pending E1`/`-- pending E3` hypotheses (E4 needed: `watcher.go:456-460`; E6 at `:462-464`). STOP before step 6.
- Not merged: `lean` (46 commits ahead at b6b1684acd); wait for 81's word on the e9e6351d9 pin bump, then merge and
  use `/shared/tmp/manifest-e9e.json`.
- Pitfalls: `isplitr` with no list sends ALL spatial hypotheses to the right goal (pure-left splits are fine; use
  `isplitl [H]` to keep H on the left); `unfold X` in an Iris goal unfolds X in every hypothesis too (use
  `iunfold X at H`); `statusFailureAt` has no `Persistent` instance; `List.reverseRecOn` does not exist here
  (induct on the length, `List.dropLast_concat_getLast`); `BigSepL.bigSepL_intro` needs `Intuitionistic`, which a
  mono-list lb does not get: use `bigSepL_forall_elim`.

## START HERE (2026-11-15, fourteenth 7f-5 agent): error leaves done; step 4 in progress

81's decisions (questions.md, 2026-11-15, fourteenth agent): InfoS stays a callee hypothesis (Go test
`examples/premisefix/watcherctx/infos_test.go`, passes; axiom at step 7); the error leaves over an internal
predicate; E1-E6 drafted only (`notes/k8s-7f5a-draft.md` §11).

- **Done** (`02e9261728`): `k8s.kErrOk err` (`WatchDefs.lean`, section `errs`: comparable dynamic type,
  `Error()`/no `Format`, `etcdError.Code`, `grpcError.GRPCStatus().Code`, `errors.As(&corrupt)` false,
  `APIStatus.Status` a Failure) with `wp_kErrOk_eq` (the comparison where `go_eq_interface` leaves it:
  `wp_bind (ite _ _ _); iapply wp_kErrOk_eq $$ Heq`); `isCancelError`, `interpretWatchError`,
  `transformErrorToEvent` (post: the event and the status owned; the caller persists the status for
  `statusFailureAt`), `logWatchChannelErr` proved, no new text. `StatusError.Status` translated with its
  body (`errors.toml`; rebuilds most of the tree).
- **Step 4, proved** (`549e1d6d6b`, `ab9ba4fa16`; targeted `lake build` green, 7458 jobs,
  `/shared/tmp/k8s7f5a-p2/build-step4.log`): `watchChan.queueEvent` (generic in the SPSC protocol and in `cdw`),
  `watchChan.sendEvent`, `watchChan.sendError` (an abstract send commit `£1∗£1∗£1 -∗ ∀ Φ, ▷ (Q -∗ Φ) -∗
  sendAu γch v Φ`; sendError also `context.cancelSpec cf γc Pc ∗ □ Pc`). Not yet: the `resultChan` protocol
  lemma that discharges the abstract commit (below), and `kResInv`'s ghost steps (send, filter, error).
- **Finding (design, not a Draft statement): `resultChan`'s two producers cannot use `spsc_send_au`.** It takes
  the producer token and `P sent.length v` before the send, and every invariant is at `nroot` (`isSpsc` too),
  so `kResInv` cannot be opened at the commit. Route (no Draft or Perennial change): allocate ONE invariant
  `inv nroot (spscInv γ.res (kResElem …) R ∗ kResInv …)`, give the consumer `isSpsc` by Iris's `inv_split_l`,
  and prove a local send lemma (a copy of `spsc_send_au`'s proof, `Spsc.lean:405`, taking the token and the
  element's `P` from `kResInv` inside the opened invariant). That lemma discharges sendEvent/sendError's
  abstract commit (`Hsend`). Not written yet.
- **Next, in order:** (1) the combined-invariant send lemma (`spsc_send_au_inv`, a local copy of
  `Spsc.lean:405-532` with the token and `P` taken from `X` at the SndPending/RcvPending/Buffered commits and
  the closed states refuted by `X`'s token; notes/perennial-changes.md entry has the statement) and `kResChan`
  (`isChan ∗ inv nroot (spscInv γ.res (kResElem …) R ∗ kResInv …)`, `inv_split_l` for the consumer's `isSpsc`);
  (2) `kResInv`'s ghost steps as lemmas: a processor send (raws ++ [r], evs ++ [e], `kStreamSub_of_raw`, pick
  the larger-revision `σ` by `kRawStreamRel_hist`), a filtered raw event (raws ++ [r] only), an Error event
  (evs ++ [err]); (3) step 5 (`sync`/`syncPaginated`, `startWatching`; `kErrOk` of each error it sends needs
  E2-E5, §11: STOP there for 81 if a text is needed). Proof patterns: `Reflector__startResync.lean`
  (`HDone` + `wp_select_blocking`), `watchGRPCStream__unicastResponse.lean` (send clause); credits: `wp_apply_core
  time.wp_Now; iintro %t -; wp_auto_lc 3` (a `wp_apply` already runs `wp_auto`, leaving no pure step). Pitfalls: `cases h : go.typeSetContains …` also rewrites the Iris hypotheses' premises
  (then `Hcode $$ %trivial`); `wp_method_call` rewrites the first `methods` in the goal, Iris context included
  (clear hypotheses mentioning other methods first); a `fmt.argOk` hypothesis is not persistent (`ihave H`, and
  name it in `wp_apply … $$ [$Hsl H]`); `--goal L` needs a column inside the tactic (`L:2`).

## START HERE (2026-11-15, thirteenth 7f-5 agent): step 3 leaves done but the error leaves; STOPPED on the error design (E1-E6) and InfoS

- **Proved** (Spec + Proof each, lean-checked, targeted `lake build` green, no `sorry`): `watchChan.transform`
  (`29741e6a08`; callees `prepareObjs`, `filter`, `acceptAll`); `flowcontrol.initializationSignalFrom`,
  `flowcontrol.WatchInitialized` (new `Spec|Proof/k8s_io/apiserver/pkg/util/flowcontrol/`; over T5-b's
  `valueAt … initSignalRes`); `watcher.getStartWatchResourceVersion` (the `getCurrentStorageRV` call as a WP
  premise with a caller-chosen post `R`); `store.watchContext` (any triple of `WithRequireLeader(ctx)` is one of
  it); `newBlockLogger`, `blockLogger.recordWait` (`d1e55060b8`; WatchDefs gained `clockNowOk`,
  `blockLoggerInv` (lastLogTime/eventCount/timeWaiting under `mu`), `blockLoggerOk` (persistent, stated under
  `□`: the instance search failed on the bare `∃`, cause not found).
- **Candidate text, not an axiom:** `Spec/k8s_io/klog/v2/Verbose__InfoS.lean` (`klog.Verbose.InfoS.spec`,
  restricted to keys/values of type string/int/Duration/GroupResource), a callee hypothesis of
  `recordWait.wp_proof` (as `StringPtr.spec` for `parseEvent`). Needs 81's axiom review before step 7.
- **Not done, blocked (decision asked, questions.md):** `isCancelError`, `logWatchChannelErr`,
  `interpretWatchError`, `transformErrorToEvent`, hence step 4's `sendError` and step 5. The Draft (§5,
  "expected to need no new text") is wrong here: see questions.md, 2026-11-15 thirteenth agent, E1-E6.
- **Not started:** step 4 (`queueEvent`, `sendEvent` could go now: they need only `recordWait`, `time.Now/Since`
  and the select pattern of `watchGRPCStream__unicastResponse.lean`; `sendError` waits on E1-E6), step 5.
- Pitfalls: `--goal L` shows the state *before* line L; a WP hypothesis (not a triple) is applied with
  `wp_bind (App (Val _) (Val _)); iapply (wp_wand) $$ [H]`; `wp_apply X ?_ $$ …` leaves the pure `?_` goal first
  (no `rotate_left`); a slice literal's list is `[..].set (sint.nat (W64 (0+1))) …`: rewrite each index by `rfl`
  then `List.set_cons_succ/zero`; never `pkill -f` a pattern that occurs in your own command line (it kills the
  shell); the lean-check server can sit at "line 1" for 40 min when an import fails to build: build the import with
  `lake build` to see the error.

## START HERE (2026-11-15, twelfth 7f-5 agent, final): A-C done and built; prepareObjs proved; next `transform`

- Full build after B/C: green but for the draft then in `watchChan__prepareObjs` (`/shared/tmp/k8s7f5a-p2/full2.log`;
  the only other break, `validateRevisions`' `simp only [eventAt]`, fixed); `gen-interface --check` of every
  `etc/api` list: no change. `watchChan.prepareObjs` proved since (`ab00296694`; callees `decodeObj`,
  `acceptAll`; `ObjCodec.dec_nil`/`ne_nil_of_dec` give the non-empty previous value).
- **Next, in order:** `watchChan.transform` (spec written, `Spec/.../etcd3/watchChan__transform.lean`; proof: cases
  on `r` as in `prepareObjs`; bookmark: `newItemOk`'s zero object, the versioner's `UpdateObject` at `W64 r`,
  `watchContractOk`'s annotate when `ann`; `.kv`/`.ev`: `filter`/`acceptAll` specs and `kRawToEv`/`kEvOfL` by
  `simp` with `kDec_some`'s `hko`; the revision premise turns `W64 (sint.nat rev)` back into `rev`; `recordTimestamps
  ↦□ false` skips the wrap). Then the error/logging leaves, `getStartWatchResourceVersion`, `WatchInitialized`,
  `watchContext`, `newBlockLogger`/`recordWait` (a mutex: a lock invariant over the logger's fields, `klog.V(3).InfoS`
  and the clock's `Now`/`Sub` at the trust boundary: check what specs exist before designing), then steps 4-5.
  Step 4's `select` send/`ctx.Done()` pattern: `client/v3/watchGRPCStream__unicastResponse.lean`
  (`chan.wp_select_blocking`, `sspsc_send_au`).
- Pitfalls added: in the `.ev` cases `simp only [hc, ↓reduceIte]` on the goal rewrites the hypotheses' facts too
  (then `rw [Hdel]`, not `rw [Hdel, hc.1]`); `rw [← Hrev]` after the `simp` of the post, not before (it rewrites
  `e.kv.modRev` inside the conditions); `omit [DecidableEq Obj] in` for `Contract.lean` lemmas used over a
  spec's `Obj`.

## (superseded) twelfth 7f-5 agent, later: 81 decided A-C; B and C done in the tree (build pending)

- **(A)** goose proposal written: `notes/perennial-changes.md`, "Goose: the pointer method of an axiomatized value
  method"; `StringPtr.spec` stays a callee hypothesis of `parseEvent.wp_proof` until the pin moves (step 7).
- **(B)** `EtcdGrove.eventAt` (`cache/v3/InvStore.lean`) ends with `⌜ev ≠ null ∧ e.kv ≠ null⌝`; new law
  `eventAt_nonnull`; `eventAt_elim` keeps its statement; producer `WatchContent.evIs_facts` (from `mvcc.evRd`'s
  `%Hn`); every reader's `iunfold eventAt at H` became `ihave H := eventAt_elim $$ H` (patterns unchanged);
  ledger 2026-11-15 (B).
- **(C)** `ObjCodec.fromS_nil_decode : ∀ d st, fromS [] = some (d, st) → decode d = none` (docstring: Kubernetes
  codecs reject empty data), laws `ObjCodec.dec_nil`, `ObjCodec.ne_nil_of_dec`; discharged for `driverCodec`
  (`examples/k8s/etcd3/Codec.lean`, `decodeD []` is `none`); Go check in `TestCodecDecodeNil`
  (`examples/k8s/etcd3/list_test.go`, passes); ledger 2026-11-15 (C).
- `Contract.lean` gained `Persistent` instances for `versionerOk` and `transformerOk`.
- **WatchDefs** gained `kCurObj`, `kOldObj`, `kRawDecOk`, `kRawRev`, `kObjOpt` (prepareObjs' results).
- **Written, not yet checked:** `Spec/.../etcd3/watchChan__prepareObjs.lean` (+ proof skeleton with `sorry`),
  `Spec/.../etcd3/watchChan__transform.lean` (no proof yet; its premises: `kRawDecOk`, revisions not negative,
  `recordTimestamps ↦□ false`, `newItemOk`).
- Full build after B/C: `/shared/tmp/k8s7f5a-p2/full1.log` (started before the `Contract.lean` instances and the
  WatchDefs additions: rebuild once more).

## START HERE (2026-11-15, twelfth 7f-5 agent): step 3 partly done; STOPPED on three decisions (A-C)

- **Proved** (Spec + Proof each, lean-checked, no `sorry` but the hypotheses noted): `mvccpb.Event.IsCreate`,
  `Event.GetType`, `Event.GetKv`, `KeyValue.GetCreateRevision`, `KeyValue.GetModRevision`
  (`Spec|Proof/go_etcd_io/etcd/api/v3/mvccpb/`, premise `p ≠ null`); `parseEvent` (premise `p ≠ null ∧
  e.kv ≠ null`; callees `IsCreate`, EtcdGrove's `fmt.Errorf.spec`, and `mvccpb.Event_EventType.StringPtr.spec`,
  a new spec with no proof yet: (A)); `decodeObj` (premise `S.decode d = some o`); `watchChan.filter`,
  `watchChan.acceptAll` (over `internalPred ↦□ p ∗ selPredOk`). Commits `f92d9cc133` and the next one.
- **Decisions asked of 81** (questions.md, 2026-11-15 twelfth agent): (A) discharging `StringPtr.spec` (goose
  emits no `ptr_M_unfold` for an axiomatized value method); (B) `EtcdGrove.eventAt` should carry `ev ≠ null ∧
  e.kv ≠ null` so that `startWatching` can call `parseEvent` (step 5); (C) empty stored values: `kvWfHist`
  does not exclude a decodable empty value, for which `prepareObjs`/`transform` differ from `kEvOfL`
  (prevValue dropped, `filter(nil)`): `prepareObjs`'s and `transform`'s specs wait on it.
- **Next, in order (after 81's answers):** `prepareObjs` (premise: the event's values decode, from `kvWfHist`
  and (C); its error paths, hence `transformIfCorruptObjectError`, are then unreachable), `transform` (versioner
  `UpdateObject` of `newFunc()`'s object, `AnnotateInitialEventsEndBookmark` from `watchContractOk`; the
  `recordTimestamps` wrap is off by premise), then `isCancelError`, `logWatchChannelErr`, `interpretWatchError`,
  `transformErrorToEvent`, `newBlockLogger`, `recordWait`, `getStartWatchResourceVersion`, `WatchInitialized`,
  `watchContext`; steps 4, 5 as below.
- Pitfalls: `wp_if_destruct`'s first goal is not always the true branch (read the `Hif` it adds); `wp_auto`
  after a `wp_apply` whose post was a value fails with "no progress"/"not a WP": use `(try wp_auto)`;
  `fmt_args_intro` only rewrites the slice literal's index 1 (for three arguments add
  `rw [show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl]` first); `versionerOk`/`watchContractOk`/`selPredOk`
  have no `Persistent` instance on the name: `unfold` them before `wp_start` and destructure there.

## START HERE (2026-11-15, eleventh 7f-5 agent): 7f-5a-P step 2 done, step 3 started

- **Step 2 rest** (`601ff6080f`, `WatchDefs.lean` §"Along one history"): `kvSameHist_changesAt`/`_revEvents`,
  `kRangeEvsL_hist`/`_mem`, `kRawRevOk` (an etcd event's mod revision ≤ the state's: `transform` reads the
  same at a longer state, `kRawToEv_hist`, `kRawToEv_filterMap_hist`), `kRawTail_hist`, `kRawIdealL_hist`,
  `kRawStreamRel_hist` (any relation), `kRawStreamSub_revOk`, `kRawStreamOk_sub`, prefix closure
  (`kRawStreamOk_prefix`, `kRawStreamSub_prefix`, `kRawStreamSub_sublist`), **segments** `KRawSeg σ inS c c' s`
  (the raw events between two cursors: `kRawSeg_tail`, `_append`, `_chg1` (a response's events),
  `_bm1` (a progress notification), `_hist`, `_le`), `inRange_scope` (the client range is `kInScope`;
  needs a non-empty key when recursive), `rangeEvents_scope`. The initial events from pages: use
  `ListPages.lean`'s `fromL`/`fromL_next`/`fromL_kp` in step 5 (syncPaginated's pages are `pageOp`'s up
  to the option order).
- **The Draft's §2/§4 vocabulary moved to `WatchDefs.lean`** (namespace `k8s`; the Draft keeps only the
  triple). `eventAt σ p r := ∃ ev, p ↦□ ev ∗ kEvIs σ ev r` (`kEvIs` the old match, so leaf specs hand an
  owned `p ↦ ev ∗ kEvIs σ ev r`). New `kFmtErr err` (what `fmt.Errorf` gives).
- **Translation:** `Event.IsCreate` (mvccpb, with `GetType`/`GetKv`/`GetCreateRevision`/`GetModRevision`
  and `PUT`) now translated with bodies (`Code/go_etcd_io/etcd/api/v3/mvccpb.toml`, `etc/goose.py --project
  etcd --perennial /shared/perennial-ddc0f0acc`): `parseEvent` calls it, and it was names-only. `PUT` was an
  axiom, now a def: check `tcb --check`. This rebuilds most of the tree.
- **Step 3, proved** (`d801decb87`, Spec + Proof each, no `sorry`): `progressNotifyEvent`, `parseKV`,
  `isInitialEventsEndBookmarkRequired`, `areInitialEventsRequired` (pattern: `featuresInit` → `featureGateOk`'s
  `Enabled` triple, `watchListOn`'s gate agreed by `typedPointsto_agree_wand`; `cases sie`, `sendInitIs`
  unfolded, `typedPointsto_not_null`; a byte-slice key to `storageKey`: `wp_bytes_to_string`).
- **Next, in order:** (1) `parseEvent`: its spec is written, uncommitted, at
  `Spec/k8s_io/apiserver/pkg/storage/etcd3/parseEvent.lean` (pre: the cache's `EtcdGrove.eventAt p e`,
  `eventIs e ev`, the `PrevKv` field, `prevKvOk o σ ev e.prevKv`; post: an owned `kEvIs σ x (.ev ev)`, or
  `err ≠ nil ∧ e.prevKv = null ∧ ¬ v3rpc.evIsCreate ev` with `kFmtErr err`). Its callees need specs first:
  `mvccpb.Event.IsCreate` and the four getters (`Event.GetType`, `Event.GetKv`, `KeyValue.GetCreateRevision`,
  `KeyValue.GetModRevision`), one Spec/Proof pair each under `Spec/go_etcd_io/etcd/api/v3/mvccpb/` (now
  translated); `time.Now` (`time.wp_Now`), `fmt.Errorf` (`fmt_args_ok`; `%q` of the key string, `%d` of
  the int64, `%s` of `Event_EventType.String()` reached through the pointer method rule on the field's address,
  T5-f's axiom). (2) The rest of the step-3 list (Draft §6): `decodeObj`, `prepareObjs`,
  `transformIfCorruptObjectError`, `filter`, `acceptAll`, `transform`, `isCancelError`, `logWatchChannelErr`,
  `interpretWatchError`, `transformErrorToEvent`, `newBlockLogger`, `recordWait`,
  `getStartWatchResourceVersion`, `WatchInitialized`, `watchContext`. Then steps 4, 5 (stop before 6).
- Checks owed before any land: `etc/gen-init.py --check` (mvccpb's translation changed; its initializer did
  not), `etc/goose.py --check`, full build (the mvccpb change rebuilds most of the tree: a lean-check of one
  leaf took 22 min the first time), `tcb --check` (`PUT` went from an axiom to a definition).
- The Draft's header still describes the moved vocabulary; fix it when the triple moves to `Spec/`.

## START HERE (2026-11-15, tenth 7f-5 agent, final): M1 LANDED (lean `2dbf6503cc`); 7f-5a-P steps 1-2a done

- M1 landed via `etc/land.sh` (lean `2dbf6503cc`, gates all passed, `/shared/tmp/k8s7f5a-p/land.log`).
- **Step 1** (`920165edf8`): `etcd3.toml` translates `parseEvent` and `watchChan.startWatching` with bodies;
  `runtime.toml` adds `Decode` (body: `d.Decode(data, nil, nil)`); `etc/goose.py --project k8s-apiserver
  --perennial /shared/perennial-ddc0f0acc` regenerated (`Code/` only, 2 files), `gen-init --check` ok.
  `wait.Jitter` stays names-only: T5-d (an axiom, text reviewed in `notes/k8s-7f5-freeze.md`) and T5-f
  (`klog.Warningf.spec`, `mvccpb.Event_EventType.String.spec`, the Draft's §5) are **not yet written as
  axioms**: trusted text is a hard stop of this brief; ask 81 whether the reviewed texts may go in as is
  (tcb then 870 → 873 or so, `--update` after its go). **Done after 81's go (`f42e7a9287`):** the three axioms
  written verbatim; `tcb --check` still 870/4 (no root reaches them until the store watch is linked, step 7:
  `--update` then). `Event_EventType.String` is called through the pointer type's `MethodResolve` on the
  field's address (`etcd3.lean:2623`): reach the value-receiver spec by Perennial's pointer-method rule.
- **Step 2, first part** (the commit after `920165edf8`): `Proof/k8s_io/apiserver/pkg/storage/etcd3/WatchDefs.lean`
  (namespace `k8s`) holds the Draft's pure part (§1 and the raw protocol), moved; the Draft imports it.
  Laws proved: `kRawToEv_t` (no Error event), `kTail_of_raw`, `kRawIdealL_filterMap`, `kNonErr_filterMap`,
  `kStreamOk_of_raw`, `kStreamSub_of_raw`.
- **Next, step 2 rest:** transport along `kvSameHist` (`kvSameHist_at` exists in ListDefs; needs the
  same for `changesAt` (via `take_of_prefix` and `List.getElem?_take_of_lt`) and `revEvents`; `kEvOfL`'s
  `kPrevAt` reads `σ.at (modRev - 1)`, so a revision's events need `modRev = W64 r` (`evsOfRevM`'s
  `evOfKv r`) and `σ.rev < 2^63`, so `KTail`/`KRawTail` at `σ` hold at a longer `σ'`), prefix closure,
  `inRange (pfx) (prefixEnd pfx) ↔ kInScope`, a client response (`watchStateRespOkP`: now one progress
  case with `hdrRev ≤ σ.rev`) gives a `KRawTail` chunk and its `PrevKv` gives `kPrevAt`, the initial
  events from `syncPaginated`'s pages. Then step 3 (leaves), 4 (channel ops, premise
  `isContext wc.ctx { cd with PDone := cd.PDone ∨ kCancelPD γ cd }`), 5 (producer); stop before step 6.
- Build: targeted `lake build --packages=/shared/tmp/manifest-ddc.json Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs`
  under `systemd-run --scope -q -p MemoryMax=64G`; `etc/lean-check.py` with
  `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`. goose: `--perennial /shared/perennial-ddc0f0acc`
  (the worktree has no `.lake/packages/perennial`), GOWORK unset.

## START HERE (2026-11-15, tenth 7f-5 agent, later): M1 done on the branch; STOPPED before land.sh

81 decided M1 (questions.md 2026-11-15): the client spec strengthened. Done (`0e0f6c771e`, lean
`6c7ff6d645` merged in `7d0e5b97d8`; ledger entry "the client watch's progress notification at the
watch's start"): `rawRespOk`'s and `watchStateRespOk`'s progress arms lost their start disjuncts (always a
certified log / `hdrRev ≤ σ.rev ∧ no range event ∧ kvLogOkTo`); `cmpl_cov`/`cmpl_prog` keep the log;
`raw_to_state`, `posQ_of_resp`, `KMWatch` (`watchRespOk_of_state`), examples `watch/StateResp` repaired.
Checks: full build 17554 jobs (`/shared/tmp/k8s7f5a-p/full2.log`), `etc/gates.sh` all passed
(`/shared/tmp/k8s7f5a-p/gates.log`: tcb 870/4, 58 collections, bounds 351, mode 447, interfaces ok: no
interface diff, there is no client API list). **Next, on 81's go:** STATUS entry (oldest to
status-history, append only), `etc/land.sh`; then the Draft's KTail needs no change for M1 (the start
notification is now `≤ σ.rev`), and 7f-5a-P steps 1-5 (Draft §6), steps 4-5 over the premise
`isContext wc.ctx { cd with PDone := cd.PDone ∨ kCancelPD γ cd }`; stop before step 6.

## START HERE (2026-11-15, tenth 7f-5 agent): re-review fixes M2/m1/m2 done; STOPPED on M1 (client spec)

Branch `k8s-7f5` fast-forwarded to lean `7d9d727fba` (it already contained the branch); full build
17553 jobs (`/shared/tmp/k8s7f5a-p/full1.log`). 81's decisions on the independent re-review are in
questions.md (2026-11-15). Done in the Draft (`Draft7f5a.lean`, built; `notes/k8s-7f5a-draft.md` §10;
ledger entry 2026-11-15): M2 (`KWatchNames.procEx`, `kProcExited`, `kCancelPD` with it, `kInElem`'s
third disjunct), m1 (error arm), m2 (`kStartOk`: `m.req ≤ st`, the `1` from the caller's `Q`);
`notes/perennial-changes.md`'s `WithCancel` entry has 81's decision (a) and a design sketch (to go to
81 as the Perennial proposal). **STOPPED:** M1's local fix does not serve 7f-6 (questions.md OPEN
entry); waiting on 81 for the client-spec strengthening. **Next, on 81's answer:** M1's fix, then
7f-5a-P steps 1-5 (Draft §6); steps 4-5 take `isContext wc.ctx { cd with PDone := cd.PDone ∨
kCancelPD γ cd }` as a premise; stop before step 6.

## START HERE (2026-11-14, ninth 7f-5 agent): review fixes of the 7f-5a Draft done; STOPPED for 81's re-review

81 accepted D1-D7 and decided the review's fixes (questions.md, 2026-11-14). Done on `k8s-7f5`
(see the commit after `0b8c92dd0b`): `Draft7f5a.lean` restated (the no-gap prefix only while the
watch is live: `kStreamSub` always, `kStreamOk` unless `kCancelled γ cd := kStopped γ ∨ □ cd.PDone`;
`kLive`/`kStopped` with `Stop`; `kStartOk` ties the start point to a fired `□ Q lb0 σ0`; `eventAt σ`
keeps `prevValue ↔ kPrevAt`; no thread tokens; T5-f's `klog.Warningf.spec` (restricted) and
`mvccpb.Event_EventType.String.spec` as Lean statements in its §5), `notes/k8s-7f5a-draft.md` §8
(each change old → new) and §9 (items for the re-review), the Go tests
(`examples/premisefix/watcherctx/draft7f5a_test.go`: metadata and already-done parents, the UTF-8
panic asserted), `nonissues/k8s-etcd3-watcher-gap-after-cancel.md` (+ test). Built; tcb --check no
change (`/shared/tmp/k8s7f5a-fix/tcb.log`). **Next, on 81's re-review:** T5-e's Lean (restate
`WithRequireLeader.wp_proof` with `□ ∀ cd, isContext ctx cd -∗ isContext c cd`), then 7f-5a-P as in
the Draft's §6; before its step 4, settle the `WithCancel`-keeps-`PDone` gap (§6 risks); align
`klog.Warningf.spec` with `notes/klog-args-fix.md` once it exists.

## START HERE (2026-11-14, eighth 7f-5 agent): 7f-5a-D Draft written; STOPPED at S3 for etcd-grove-81

The Draft of the etcd3 watcher's serial branch is in the unlinked
`Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean` (namespace `k8s.Draft`; builds with
`lake build Proof.k8s_io.apiserver.pkg.storage.etcd3.Draft7f5a`), explained in
`notes/k8s-7f5a-draft.md` (statements §1-§4, trusted texts §5, proof plan §6, decisions D1-D7 §7).
Go evidence for the new trusted texts T5-e (`isContext` through `WithRequireLeader`) and T5-f (leaf
no-op specs): `examples/premisefix/watcherctx/draft7f5a_test.go` (passes). tcb --check: no change
(`/shared/tmp/k8s7f5a-d-tcb.log`). **Next, on 81's decisions:** if T5-e is approved, restate
`WithRequireLeader.wp_proof` (one conjunct), build, tcb --check (same count: the name is unchanged),
axiom-tok, land T5-e on its own; then 7f-5a-P in the Draft's §6 order (move the vocabulary to
`WatchDefs.lean`, the triple to `Spec/.../store__Watch.lean`, delete the Draft). Pitfalls: the
monoList ghost lists need `Pos.Countable` (Draft: `watchEvent_countable`, `kwev_countable`; `KRaw`
needs one too, today an instance argument of `kInElem`/`kResInv`).

## START HERE (2026-11-14, seventh 7f-5 agent, final): 7f-3 LANDED; next 7f-5a-D, a fresh agent

7f-3 is complete and landed (7f-3c approved by etcd-grove-81, including keeping `isRangeWatch`,
`watchStateElem`, `watchStateRespOk`, `respAt` beside the P-forms for the cache; lean hash in STATUS /
`/shared/tmp/k8s7f3c/land.log`). **Next: 7f-5a-D, the Draft of the etcd3 watcher's serial branch**
(`notes/k8s-7f5-scope.md` §6 row 7f-5a-D; the parent `notes/k8s-7f-scope.md` §9 row 7f-5a):
`store.Watch.spec`, `k8sWatch`, the list of internal specs, the protocol (the `incomingEventChan`
SPSC, `resultChan` with two producers), stated against the landed client spec: `watcher.Watch.spec`
now takes `isRangeWatchP` (the etcd3 watcher asks `WithPrevKV`) and its channel element is
`watchStateElemP` (`WatchStateDefs.lean`: each event's `PrevKv` readable through `respAtP`'s
`eventsPkAt`, its pointer `prevKvOk`: `nil` always admitted, else the key's record at `rev - 1` for a
non-create event). Go: `staging/.../storage/etcd3/watcher.go` `:546-575` (`processEvents`,
`serialProcessEvents`); the Scope's §2-§5 (context enumeration, T5-b/T5-c landed, T5-d text only,
Q6's temporary premise `ConcurrentWatchObjectDecode` off introduced here). **Hard stop S3: the Draft
for etcd-grove-81's review**; no Lean proofs before it. Worktree `/shared/etcd-grove-k8s7f`, branch
`k8s-7f5` (merge lean first). Build: see the earlier sections (flock + `systemd-run --scope -p
MemoryMax=64G`, `--packages=/shared/tmp/manifest-ddc.json`); long proofs: `etc/lean-check.py --fast --split`.

## Handoff point (2026-11-14, seventh 7f-5 agent): 7f-3c done on the branch; checkpoint (not landed)

Done on `k8s-7f5` (commits `b9e66b2591`..`cb54e77c51`; decisions in questions.md, 2026-11-14 7f-3c entry):
- Step 1: `client.rawRespOk` is the Draft's `rawRespOkP` in place (`WatchStateDefs.lean`, with
  `prevKvLogOk`, `EvModel.erasePk`, `withPk`); producers: `dispatch_content` (pointers `qs` from
  `evs_pkSent`: `pkQAt`, `pkSent` per event), `cmpl_events` (`pkSent_logOk`, with the run's `pkIs`
  from `regFacts`' new 4th conjunct `pkReg`, filled at the created response from `ctrlWatcher`);
  consumer `raw_to_state` (WatchFire) gives `watchStateRespOkP` (`prevKvLogOk_state`).
- Step 2: `recvCmpl` carries `watchStateRespOkP ∗ eventsPkAt`; `outcElem := watchStateElemP`;
  run/serveSubstream/sendCloseSubstream/WatchApiLemmas adapted; the request carries `prevKV`
  (`createOf … pk`, `wrRO`, `watchRequest.toPB.spec` with `prevKV ↦□ pk`).
- Step 3: `watcher.Watch.spec` is S6's text under the old name (`isRangeWatchP`, `watchStateElemP`);
  `watcher.Watch.wp_proof` proves it.
- Step 4: `Draft7f3a.lean` deleted; old forms kept where the cache uses them (`isRangeWatch`,
  `watchStateElem`, `watchStateRespOk`, `respAt`). Users switched: KMWatch, etcdstart RespChan
  (`isRespChan_of_state[_cmp]` take `watchStateElemP`: interface regenerated), compactor
  (`client_Watch_field` restated with the P-forms), auth Work, examples watch/compactwatch. Pattern:
  after `wp_spsc_receive`, `ihave HP := watchStateElemP_elem _ _ _ _ _ _ _ $$ HP`; a premise
  `isRangeWatch … = true` becomes `OpFull.isRangeWatchP_of h` (or `simp [OpFull.isRangeWatchP]`).
- Checkpoint: full build 17487 jobs (`/shared/tmp/k8s7f3c-full2.log`), tcb 870/4 matches
  (`/shared/tmp/k8s7f3c-tcb.log`), gates all ok but the etcdstart interface (expected; regenerated
  in `cb54e77c51`; rerun `/shared/tmp/k8s7f3c/gates2.log`). STOPPED for 81's review.

Next on 81's go: merge lean, STATUS entry (oldest to status-history, append only), `etc/land.sh`.
Then 7f-3 is complete; next stage per the Scope (7f-5's T5-c/T5-d).

## Handoff point (2026-11-14, sixth 7f-5 agent, final): 7f-3b v3rpc part LANDED; 7f-3c next (a fresh agent)

81 approved the v3rpc part as is (step 4 moved to 7f-3c, the `γpk`/`pkIs` map, the nonissue); landed
via `etc/land.sh` (hash in STATUS / the landing log `/shared/tmp/k8s7f3b-v3rpc/land.log`).

**Next: 7f-3c, the client part**, in this order (statements in `Draft7f3a.lean`, `notes/k8s-7f3a-draft.md` §5):
1. `client.rawRespOkP` in place of `rawRespOk` (`WatchStateDefs.lean`; move `prevKvLogOk` there, with
   `v3rpc.evIsCreate`). Producers (WatchRun's `prog_cmpl`/`cmpl_events`, WatchCompl, `run` ~1374) derive
   each pointer's `prevKvLogOk` from the server's `evsSentOk` (`client.mvccOk_evsSent`, `v3rpc.pkWritten`):
   for `prevKV = false`, `pkIs` of the response's id agrees (`v3rpc.pkIs_agree`, names through
   `v3rpc.auxOf_inj_pk`) with the created response's `pkIs … c.prevKv` (`ctrlWatcher`); for a written
   one, transfer `stateAt` between `pkWritten`'s `L` and the client's log by `histLb` agreement
   (`v3rpc.stateAt_prefix`), and exclude revision 1 by `L[1] = []`. Consumers (WatchFire `raw_to_state`,
   WatchResume, serveSubstream `rawRespOk_created`) read the erased-events equation.
2. The client's `watchGRPCStream.run` / `serveSubstream` / `dispatchEvent` carry the `PrevKv` pointer
   (the client copies the `*Event` pointers; today `evs_eventsAt` gives `evModelOf` with `prevKv := null`).
3. `watcher.Watch.specP` (S6).
4. Swap the old definitions (`isRangeWatch`, `watchStateRespOk`, `watchStateElem`, `respAt`,
   `watcher.Watch.spec`) for the P-forms; each user (watchkv, cachekv, linkv3p `MainWatch`, the
   compactor, `etcdstart.Collect`, `Election.observe`, recipes, auth `RootWatch`/`WorkCalls`) switches to
   `specP` and reads elements through `watchStateElemP_elem`.
Report the interface/statement changes to 81 before landing, as for 7f-3b.

## Handoff point (2026-11-14, sixth 7f-5 agent): 7f-3b v3rpc part done on the branch; checkpoint (not landed)

Done (`35fdc186ad` and the commit after it on `k8s-7f5`; questions.md entries of 2026-11-14):
- Steps 1-3, 5, 6 of the list below. `recvLoop` records `prevKV[id] = true` (`swsMu`, the Draft's
  `swsMuP` under the old name, each entry carrying `pkIs γpk id true`); `sendLoop`'s `PrevKv` branch
  (`IsCreateEvent` on `evRd`, the watchable store's `Range` at `ModRevision - 1` through
  `shapes.law`'s `KV.Range.contract` and `v3rpc.range_au`, `r.KVs[0]` written into the copy's owned
  field, the error/empty arms) inside the macro `pk_branch` (the code generator overflowed with one
  macro); `watchReqOk` without `prev_kv = false`; `wrespRO` removed.
- The server's guarantee for the client (7f-3c): `mvccOk` carries `evsSentOk r x m.evs` (`pkWritten`
  per event: mvcc's event, or with `PrevKv := some kv` for a non-create event of a watcher with
  `pkIs … true`, `kv` the key's record at `ModRevision - 1` of a certified log `L` with `L[1] = []`,
  claimed at revisions ≥ 2). The created response's `ctrlWatcher` gives `pkIs r.γpk id c.prevKv`
  (agreement: `pkIs_agree`; the client finds `γpk` through `auxOf_inj_pk`).
- Client adapted minimally (`evRd` readers, `m.evs.length = x.evs.length`); finding
  `nonissues/etcd-watch-prevkv-revision-one.md`.
- **Step 4 moved to 7f-3c** (form decision): `rawRespOkP` swap is client-only.

Checkpoint passed (2026-11-14, `de5280daab`): full build 17487 jobs, tcb 870/4, gates all passed
(`/shared/tmp/k8s7f3b-v3rpc/{full,tcb,gates}.log`), no interface diff; review material
`/shared/tmp/k8s7f3b-v3rpc/review.md`. STOPPED for 81. Next on 81's go: merge lean (it moved,
77f542f56c), STATUS entry (oldest to status-history, append only), `etc/land.sh`;
then 7f-3c: `rawRespOkP` (prevKvLogOk from `evsSentOk`: for `prevKV = false`, `pkIs` agreement with the
created response's `pkIs … c.prevKv`; for a written one, `stateAt` transfer between `L` and the
client's log by `histLb` agreement, and `L[1] = []` to exclude revision 1), then `watchGRPCStream`
carrying the pointer, `watcher.Watch.specP`, the users.

Pitfalls: in a `local macro` a `$$ [$H]` is an antiquotation (write `$$ [H]` and `iframe H`); a
`--goal` inside a macro body does not work (use a deliberate `done`); `rw … at H` on an Iris
hypothesis fails (rewrite the goal, or `irevert`).

## Handoff point (2026-11-13, fifth 7f-5 agent, final): 7f-3b mvcc part LANDED (lean `570cea0725`); v3rpc part next

Done (`3e90b6e741` on `k8s-7f5`; full build passes, 17487 jobs; tcb matches 870/4; gates all ok after
the interfaces were regenerated, log `/shared/tmp/k8s7f3b/gates.log`):
- mvcc vocabulary (`InvWatchBatch.lean`): `prevKvIs`, `evRd` (field-wise, persistent: every field but
  `PrevKv`, the key-value `kvPtrFixed`), `evPk e ev q` (the `PrevKv` field owned at a fraction: the
  lock invariant is fractional), `evOwn := evRd ∗ evPk`; laws `evIs_evRd`, `evOwn_intro` (the
  allocated copy), `evOwn_persist`/`evOwns_persist` (give the copies up: back to `evIs`),
  `evOwn_rd`, `evOwns_split`, `evRd_modRev`, `bigSepL_filter_drop`; `evPk_fractional`,
  `evOwn_fractional` (`InvWatchFrac`).
- `ownEventBatch` holds `evOwn`; `eventBatch.add`/`watcherBatch.add` take `evOwn`; `newWatcherBatch`
  makes each copy `evOwn` (`evOwn_intro`); `watcher.send` takes the copies `evOwn` and gives them back
  on `false` (post `if b then ↦*□ else ↦* ∗ [∗list] evOwn`); notify/syncWatchers/moveVictims keep
  them in the victim batches.
- Internally `respIs` keeps `evRd` (persistent); the channel invariant `watchChanInv` gains
  `"Hpk" ∷ respsPk vs (sent.drop recv.length)` (the in-flight responses' `PrevKv` fields);
  `watchRecvResult` carries `respPk v r`; every `imod Hclose` passes `Hpk`.
- API: `mvcc.api.wrespIs` carries `evOwn` (81: D2, wrespIs itself); `respIs_wrespIs` takes
  `respIs ∗ respPk`.
- Readers: `filterSpec`, v3rpc `filterNoPut`/`filterNoDelete` take `evRd`; the examples
  (`mvccfull` `stream__receive`/`stream__watch`, `mvccrand` `watchCheck__receive`) read `evRd`.
- v3rpc stopgap: `WatchApi.wrespIs_persistent` (false now) replaced by `v3rpc.wrespRO` (the old
  read-only form over `mvcc.evIs`) and `wrespIs_ro : wrespIs ⊢ |==> wrespRO`, applied at the send
  loop's two receipts. The v3rpc part of 7f-3b replaces this by the `PrevKv` write.

81 approved the interface diff and accepted `wrespRO` as temporary; landed on lean `570cea0725`
(gates all passed, `/shared/tmp/k8s7f3b/land.log`). **Next, a fresh agent: the v3rpc part of 7f-3b**, in this order (statements in
`Draft7f3a.lean`: `swsMuP`, `watchReqOkP`, `client.rawRespOkP`, `prevKvLogOk`):
1. `recvLoop` records `creq.PrevKv` in the `prevKV` map (`watch.go:342-349`): `swsMu` → `swsMuP`
   (entries allowed in `prevKV`, `fragment` still empty).
2. `sendLoop`'s branch (`watch.go:437-455`): the create check (`IsCreateEvent`), mvcc's `Range` of the
   key at `ModRevision - 1` (`Api/RangeApi.lean`), and `events[i].PrevKv = r.KVs[0]` written into the
   copy's owned field (`evPk`, from `wrespIs`'s `evOwn`), with the `nil`/error arms.
3. `IsCreateEvent`'s spec on `evRd` (today `evIs`).
4. `rawRespOkP` (the client pipeline's server contract: each pointer `prevKvLogOk`), in place of
   `rawRespOk`.
5. `watchReqOkP` in `upOk` (the server's `prev_kv = false` restriction dropped).
6. Remove the stopgap `v3rpc.wrespRO` / `wrespIs_ro` (`WatchApi.lean`) and its two uses in
   `serverWatchStream__sendLoop.lean`.
Then the client part, 7f-3c (`notes/k8s-7f3a-draft.md` §5). Report the v3rpc interface/statement
changes to 81 before landing, as for mvcc.

**Pitfall (wp_join):** after a failing bullet inside `wp_join`, later goals carry unassigned metavariables
and `wp_for`'s clean-up silently fails (`Hif : #(decide …) = #true` undecoded, `word` fails): fix the
FIRST error before reading later ones. `etc/lean-check.py` incremental runs once gave a spurious
`(kernel) application type mismatch` on `moveVictims` that `lake build` did not.

## Handoff point (2026-11-13, fourth 7f-5 agent, final): T5-a LANDED (lean `7112e7c0d6`); 7f-3b next

T5-a landed via `etc/land.sh` (gates all passed, `/shared/tmp/k8s7f3a/land3.log`): the translation of
`WithRequireLeader`/grpc metadata reverted (`WithPrevKV` kept), the restated axiom with its four-part
clause (81 accepted the `Value(&cancelCtxKey)` part), `WithRequireLeader.watchCtx_of_post` proved,
Go tests, STATUS entry. Trust base 870 axioms, 4 sorries (no baseline change).

**Next (a fresh agent): 7f-3b**, from the design section below. 81 approved: `wrespIs` itself
carries `evOwn` (not a second predicate). Order: vocabulary (`evRd`, `evPk`, `evOwn`, laws
`evIs ⊢ evRd`, the recombination to `evIs`), built; mvcc proofs bottom-up (newWatcherBatch,
eventBatch/watcherBatch add, ownEventBatch and victims, watcher.send, the three send sites, Api's
`wrespIs`, WatchLaws); **report the mvcc interface diff (`etc/gen-interface.py` for mvcc's API list)
to 81 before landing 7f-3b**; then v3rpc (`recvLoop` with `swsMuP`, `sendLoop`'s `PrevKv` branch,
`rawRespOkP`, `watchReqOkP`), then the examples/client readers. `Draft7f3a.lean` holds the S1-S9
statements.

## Handoff point (2026-11-13, end of the fourth 7f-5 agent): T5-a decomposed; land after 81 sees the flag

81 decided (a): the axiom's `watchCtx ctx s -∗ watchCtx c s` decomposed (no trunc line). Done in
`873034096c`: `Done()`/`Err()` WP transfers, **plus a `Value(&cancelCtxKey)` WP transfer (not in 81's
list: needed for `#HCC`, whose result predicate `isCancelCtxAny` is not pure, so the pure-`R` `Value`
transfer does not give it; flagged in the freeze note's T5-a review section)**, and
`metadata.outgoingCtxOkC c`; law `WithRequireLeader.watchCtx_of_post`
(`Proof/go_etcd_io/etcd/client/v3/WithRequireLeaderLaws.lean`, proved); `NewLeaseFromLeaseClient`'s
pattern updated. The three holder findings (`backend.txLive/snapRO/rtxStats`) are not from this branch
(it touches no backend file; they did not fail the gate). Build/tcb/axiom-tok results:
`/shared/tmp/k8s7f3a/{full3,tcb3,atok3}.log`: full build passes (17486 jobs), tcb matches (870/4), axiom-tok ok (0 unknown, 0 truncated).

Next, in order: 81's word on the third part; if the axiom-tok log is clean, `etc/land.sh` (with
`LAKE_PACKAGES=/shared/tmp/manifest-ddc.json`, not under GOWORK=off; re-merge lean if refused: the
etcd_auth_safe landing may be ahead); report the lean hash. Then 7f-3b per the design below (81
approved: `wrespIs` itself carries `evOwn`; report the mvcc interface diff before landing 7f-3b).

## Handoff point (2026-11-13, fourth 7f-5 agent, later): T5-a approved; land BLOCKED by the axiom-tok gate

81's review: approved as written (freeze note "T5-a review"); STATUS entry added; lean merged
(`51ee20f154`, clean; the merge adds no trusted text but ours). `etc/land.sh` (log
`/shared/tmp/k8s7f3a/land.log`): build, links, tcb (870/4 after lean's auth-schema-fix), 55 collections
ok, but **axiom-tok FAILED**: `WithRequireLeader.wp_proof`'s walk truncates ("stuck:
Perennial.context.isContextDone", inside `watchCtx`'s `#HDone` over the program-picked `s`), and
`etc/axiom-tok-allow.txt` says no `trunc` line may be added. lean unchanged. STOPPED for 81:
- (recommended) restate the axiom's first clause without `watchCtx`: `□ (∀ Φ, WP ctx.Done() {{Φ}} -∗
  WP c.Done() {{Φ}})`, the same for `Err()`, and `metadata.outgoingCtxOkC c` (the `#HCC` part is
  already the `Value` transfer at `&cancelCtxKey`); `watchCtx ctx s -∗ watchCtx c s` then a proved
  lemma outside the axiom. A trusted-text change (same meaning, more direct): needs 81's review.
- or a `trunc` entry for it (against the ratchet's rule).

7f-3b: design drafted (below), no Lean written.

## 7f-3b design (D2), started 2026-11-13 by the fourth 7f-5 agent; no Lean written yet

Go (fork pin 0b50f0426): `newWatcherBatch` (`watcher_group.go:79-96`) allocates a fresh
`&mvccpb.Event{Type, Kv, PrevKv}` per (watcher, event); the three send sites
(`watchable_store.go:309` moveVictims, `:401` syncWatchers, `:490` notify) send `eb.evs`, the batch's
own copies; v3rpc's `sendWatch` (`watch.go:437-455`) writes `events[i].PrevKv = r.KVs[0]` into
those copies (`events[i] = evs[i]` copies the pointer only). So each event a watcher receives is
owned by that watcher's response, but the Kv it points at is shared.

Proposed vocabulary (mvcc, `InvWatchBatch.lean`, exported through `Spec/.../mvcc/Api.lean`):
- `evRd e ev` (persistent): `e ≠ null`, every field but `PrevKv` `↦□` (state, Type = evType ev,
  Kv = p ≠ null, unknownFields, sizeCache), `kvPtrFixed p ev.kv`. Law `evIs e ev ⊢ evRd e ev`.
- `evPk e ev` (owned): `∃ q, PrevKv-field ↦ q ∗ (match ev.prevKv with none => q = null | some pk => kvPtrFixed q pk)`.
- `evOwn e ev := evRd e ev ∗ evPk e ev`; law: `evOwn e ev` with the field discarded gives back
  `evIs e ev'` (struct recombination: typedPointsto combine), for the send loop's handover to grpc.
The store's shared events (`kvsToEvents`, `rangeEvents`, `End`, the `notify`/`syncWatchers`
arguments) stay `evIs`; `newWatcherBatch`'s post, `eventBatch.add`/`watcherBatch.add`,
`ownEventBatch` (and the victims), `watcher.send`'s pre (events owned; on success handed to the
channel, on failure kept) and `wrespIs` (mvcc API: the channel's responses) take `evOwn`.
Readers of the fields (`IsCreateEvent`, `filterNoPut`/`filterNoDelete`, `eventBatch.add`'s
`Kv.ModRevision`, client `WatchContent.evIs_facts`) move to `evRd`.

Files (from grep of evIs/wrespIs/ownEventBatch/ownWatcherBatch): mvcc `InvWatchBatch`, `InvWatchFrac`,
`InvWatchStore`, `MoveVictimsLemmas`, `WatchSendLemmas`, `eventBatch__add`, `watcherBatch__add`,
`newWatcherBatch`, `watcher__send`, `watchableStore__{notify,syncWatchers,moveVictims,cancelWatcher,watch}`,
`watchableStoreTxnWrite__End`, `kvsToEvents`, `Api/WatchLaws`, `Spec/.../mvcc/Api.lean` (wrespIs: the
API change, interface diff); v3rpc `WatchApi`, `serverWatchStream__sendLoop`, `PerTypeWatch`,
`InvWatchStream`, `WatchLemmas`, `filterNoPut/Delete`, `IsCreateEvent` (specs); examples mvccfull
`stream__receive`/`stream__watch`, mvccrand `watchCheck__receive`; client `WatchContent`, `WatchRun`.

Open question for 81 (recommend (a)): (a) `wrespIs` carries `evOwn` (non-persistent; the channel's
element predicate hands it over), or (b) a second response predicate for the PrevKv fields beside a
persistent `wrespIs`. Order: vocabulary + laws first (built), then mvcc proofs bottom-up, then the
interface diff (STOP before landing per 81), then v3rpc's recvLoop/sendLoop with `swsMuP`.

## Handoff point (2026-11-13, fourth 7f-5 agent): T5-a fallback done; STOPPED for 81's axiom review

Done (on `k8s-7f5`, not landed; lean has moved on, merge it before landing):
- `17c793098e`: translation of `WithRequireLeader` and grpc metadata's helpers
  reverted, `WithPrevKV` kept; `etc/goose.py --project etcd`, `--check` pass; `etc/gen-init.py`
  (`--check` passes; metadata `Init` and the `PkgTable`s back to lean's); metadata's SpecPlan PkgInit
  back. Untracked SpecPlan PkgInit files the generator created (older drift on lean, listed in
  `/shared/tmp/k8s7f3a/specplan-untracked-drift.txt`) are left untracked, not committed.
- `fddf2cdf9b`: `WithRequireLeader.spec` restated (pre `watchCtx ctx s ∨ ⌜ctx = backgroundCtxVal⌝`;
  post `watchCtx ctx s -∗ watchCtx c s`, the WP and chain `Value` transfers for keys not of
  `mdOutgoingKey`'s type, and the old `WithCancel(c)` triple under `⌜ctx = backgroundCtxVal⌝`);
  `NewLeaseFromLeaseClient` adjusted (an arbitrary `s`, the right disjunct); `specGen` removed from
  `Draft7f3a.lean`; Go tests `examples/premisefix/watcherctx/requireleader_spec_test.go` (all pass);
  freeze note "T5-a addendum"; Scope §8 Q2 superseded; questions.md entries.
- Full build passes; `etc/tcb-report.py --check` matches (869/4; the axiom's name unchanged, its text
  changed); details in the freeze note's "T5-a addendum", "Checks". STOPPED for 81's axiom review.

Next: 81's axiom review of the T5-a addendum; apply its fixes; `etc/tcb-report.py --check --update`
only if the text changed the baseline (expected: no line change, the axiom's name is the same);
merge lean; land on 81's go. Then 7f-3b (D2: mvcc's response contract hands over an owned `PrevKv`).

## Handoff point (2026-11-13, end of the third 7f-5 agent): S2 decided; T5-a fallback next

81's S2 decisions (2026-11-13, also in questions.md):
- **D1 fallback.** Restate `WithRequireLeader.wp_proof` (`Proof/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`,
  spec `Spec/.../WithRequireLeader.lean`) to `specGen` (now in `Draft7f3a.lean`; move it into the Spec
  file) in `withVersion.spec`'s pattern. Keep the old `Background()` clauses (`libCtxOk`, `outgoingCtxOkC`
  after `WithCancel`) as a proved corollary, or keep them in the axiom if a corollary is not derivable;
  the lessor's caller must keep working. Go tests in `examples/premisefix/watcherctx` or a sibling:
  every key that is not `mdOutgoingKey` answers as the parent does, through `Value` and the chain;
  Done/Err/Cause are the parent's; same descriptor. Supersede Q2 in questions.md and in
  `notes/k8s-7f5-scope.md` §8 (reason: translation needs 3-4 trusted changes vs 1).
- **Revert the translation** of `WithRequireLeader` and grpc metadata's helpers (`NewOutgoingContext`,
  `Pairs`, `MD.Copy`, `MD.Set`, `copyOf`, `mdOutgoingKey`, `rawMD`, and the imports): restore
  `Code/google_golang_org/grpc/metadata.toml` to lean's, drop `WithRequireLeader` from
  `Code/go_etcd_io/etcd/client/v3.toml`, **keep `WithPrevKV`**; then `etc/goose.py --project etcd`,
  `--check`, `etc/gen-init.py` (metadata Init + PkgTables go back), metadata's SpecPlan PkgInit
  (`etc/gen-specs-pkginit.py`, keep only that file's change). Nothing else needs them (checked: only
  `WithRequireLeader` calls them).
- **D2 yes:** in 7f-3b the mvcc response contract hands over an owned `PrevKv` field per event; list the
  interface diff for review at landing.
- **D3 yes:** `specGen` without the metadata content.
- S1-S9 stay as drafted (`Draft7f3a.lean`, unlinked).

Next, in order: revert the translation as above; the restated axiom with its Go tests (Addendum in
`notes/k8s-7f5-freeze.md`, "T5-a"); build (targeted, then full under flock); `etc/tcb-report.py --check`
(expected: same count, `WithRequireLeader.wp_proof` changed text; collections that reach it);
STOP for 81's axiom review. Then 7f-3b.

## Handoff point (2026-11-13, third 7f-5 agent): 7f-3a at S2 (STOPPED for 81's review)

Done (on `k8s-7f5`, not landed):
- Translation config (Q2) applied: client `WithPrevKV`/`WithRequireLeader`; grpc metadata's
  `NewOutgoingContext`, `Pairs`, `MD.Copy`, `MD.Set`, `copyOf` (imports context/strings/fmt);
  `etc/goose.py --project etcd`, `--check` passes; `etc/gen-init.py` (metadata Init + 17 PkgTables);
  SpecPlan PkgInit for metadata only (the generator's other drift is lean's, ungated, left alone).
  The axiom `WithRequireLeader.wp_proof` still stands over the translated function.
- `EvModel` gains `prevKv : Loc := null` (InvStore.lean; InvWatcher's countable instance updated).
- The statements: `Proof/go_etcd_io/etcd/client/v3/Draft7f3a.lean` (unlinked; `P`-suffixed new
  forms + `WithRequireLeader.specGen`; laws proved, no sorry/axiom), the Draft
  `notes/k8s-7f3a-draft.md` (table old → new, findings, plan, decisions D1-D3).
- Findings: (1) Q2's "no new axiom" is false: translating WithRequireLeader needs WithValue.spec
  at grpc's key (+ valueCtx fields, watchCtx), an intro law for opaque builtRawMD (ToLower too weak
  for its case clause), FromOutgoingContext over a non-isContext parent; recommended the fallback
  (one restated axiom). (2) 7f-3b: the send loop writes `PrevKv` into mvcc's events, which mvcc's
  API gives read-only (`evIs`): an mvcc API ownership change.

Checks: full build passes (16 min, `/shared/tmp/k8s7f3a/full.log`); `etc/tcb-report.py --check`
matches the baseline (869 axioms, 4 sorries); `etc/goose.py --check` passes.

Next (after 81's decisions D1-D3): 7f-3b (mvcc event ownership, v3rpc recvLoop/sendLoop), 7f-3c (client, swap, users).

## Handoff point (2026-11-13, second 7f-5 agent): S1 LANDED (lean `be36a0f818`); 7f-3a next

S1 with the review's fixes landed (`0d873a9ee5`, `be36a0f818`; freeze note "S1 review"; gates all
passed; trust base 869 axioms, 4 sorries). The branch `k8s-7f5` is lean now; continue on it.

**Next: 7f-3a's statements, up to hard stop S2** (Scope §6 row 7f-3a; parent `notes/k8s-7f-scope.md`
§2.3 1-2, §5.1). Nothing of 7f-3a written yet. In order:
1. Translation config (no trust; from `/shared/tmp/k8s7f5/goose-dry-full.patch`):
   - `Code/go_etcd_io/etcd/client/v3.toml`: add `WithPrevKV`, `WithRequireLeader` to `translate`;
   - `Code/google_golang_org/grpc/metadata.toml`: `translate = ["!*", "NewOutgoingContext", "Pairs",
     "MD.Copy", "MD.Set", "mdOutgoingKey", "rawMD", "copyOf"]` (**copyOf**: the S1 review),
     `imports = ["!*", "context", "strings", "fmt"]`;
   - `etc/goose.py --project etcd` (not with GOWORK=off), `--check`.
   - Consequence to handle: `WithRequireLeader` is today names-only with an axiom
     (`Proof/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`, `Background()` only). Translated, that
     axiom becomes a proof over `FromOutgoingContext` (existing spec), `Pairs`/`NewOutgoingContext`
     (translated: `context.WithValue`) and `strings.ToLower` (trusted: some string): the trust base
     loses an axiom (report it; `--check --update` after 81's review). The generalized triple over a
     `watchCtx` parent (T5-a: every other key, Done/Err/Cause the parent's; the metadata "the
     parent's plus one key") is a 7f-3a statement.
2. The statements (Lean text in a Draft note, e.g. `notes/k8s-7f3a-draft.md`, for 81's S2 review;
   no `sorry` under a linked result, so do not change linked definitions before the review):
   - `OpFull.isRangeWatch` (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:1231`) drops
     `o.base.prevKV = false`; `wrRO`'s `prevKV ↦□ false` (`client/v3/InvWatch.lean:846,859`) becomes
     the model's value;
   - `EvModel` (`cache/v3/InvStore.lean:185`) gains `prevKv : Loc` (null = none); `eventAt`
     (`InvStore.lean:1214`) gains the `PrevKv` field; `eventIs` (`client/v3/WatchStateDefs.lean:102`)
     gains: `prevKV = false → prevKv = null`; else null (always admitted:
     `issues/etcd-watch-prevkv-before-created.md`), or, for a non-create, `kvValAt prevKv` of the
     key's kv at `ev.rev - 1` (`σ.at (r-1)`, as `KVState.revEvents`); a create's is null;
   - `rawRespOk` (`WatchStateDefs.lean:261`) the same at the server's level (`mvcc.stateAt L (r-1)`);
   - the server: `swsMu` allows `prevKV` entries (`v3rpc/InvWatch.lean`), `recvLoop` records
     `creq.PrevKv`, `sendLoop`'s branch `watch.go:442-455` (`watchable.Range` at `ModRevision - 1`).
   - Callers passing `prevKV = false` must see no change (watchkv, cachekv, linkv3p `MainWatch`, the
     compactor, `etcdstart.Collect`).
3. STOP (S2): report the statements and the config's trust-base effect.

## Handoff point (2026-11-13, end of the first 7f-5 agent's context): S1 reviewed; fixes next

S1 (`c46c52934c`) passed 81's axiom review with one MAJOR and minors. **Do these, in order** (81's
decisions, verbatim in the worktree's `questions.md`, last entry; review journal
`/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_115e23d1-72c/journal.jsonl`):

1. **T5-c (MAJOR).** In `Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean`, do not quantify the `Set`
   triple over every `b`. Add a table in the trusted text giving one fixed value per feature
   (`WatchList ↦ true`, every feature B5 covers ↦ `false`, e.g. `k8sSetValue : GoString → Option Bool`
   or two lists), and specify `Set(setArg s v)` only for `s` with its table value `v`. Then
   `featureOn`/`featureOff` of one feature are unreachable by construction (`featureSet g s v` for the
   one `v`). Restate the header's assumption: no other mutator runs; repeats of the same value are
   harmless. Drop "before any Enabled" if no triple needs it (none should). Callers to adjust:
   `noStreaming.lean`, `watchList.lean` (the side condition becomes the table lookup).
   Add `ResetFeatureValueToDefault` and `AddDependencies` to the mutator lists (Gate.lean header,
   freeze note S0.4, the grep). Make the closure check cover `examples/k8s/daemonset/dsmain` too, or
   state with evidence why it is outside. Turn the check into a script (e.g. `etc/featuregate-check.py`:
   `go list -deps` of the k8s examples, grep the mutators, compare to an allow-list with each hit's
   verdict) and wire it into `etc/gates.sh` (B5 has no gate today, as far as this agent saw; add one
   for both). The S0.4 grep command is in this agent's history: closure via `go list -deps -f` with
   GoFiles, regex over `DefaultMutableFeatureGate\.(Set|SetFromMap|OverrideDefault|SetEmulationVersion|Add)|\.SetFromMap(WithLogger)?\(|OverrideDefault(AtVersion)?\(|SetEmulationVersion|DeepCopyAndReset|featuregatetesting|ReplaceFeatureGates|AddFeaturesToExistingFeatureGates|DefaultMutableFeatureGate *=|DefaultFeatureGate *=`
   (hits saved in `/shared/tmp/k8s7f5/k8s-mutator-hits.txt`).
2. **T5-c docstring (minor 3).** Gate.lean's `Set` error branch says "changes nothing `Enabled`
   reads": inaccurate in Go (a failed `Set` stores the raw pair in `enabledRaw`, poisoning later
   `Set`s: `feature_gate.go:500-504`; `watcherctx` scenario `failed-set`). Reword (what is true: the
   map `Enabled` reads, `enabled`, is not stored; `enabledRaw` is).
3. **T5-a (minor 2).** Add grpc metadata's `copyOf` to the translation config (in the dry-run patch
   `/shared/tmp/k8s7f5/goose-dry-full.patch` for 7f-3a; no new trust). State the Lean result honestly
   ("parent's metadata plus one key": `strings.ToLower` is trusted to return some string), or fix it.
   Strengthen `examples/premisefix/watcherctx/requireleader_test.go`: a non-trivial `Cause` (a parent
   cancelled with `WithCancelCause(errX)`: the child's `Cause` is `errX`), and a NoAlias test that would
   fail without `Copy` (e.g. a parent `MD` whose `hasleader` key exists with another value, or check
   that writing the child's `MD` slice does not change the parent's).
4. **S0.1 (minor 4).** In `notes/k8s-7f5-freeze.md` §S0.1, add the row `getCurrentStorageRV(ctxRL)`
   (`watcher.go:146,193-209`; `store.go:240,735`: with RV 0, WatchList on and SendInitialEvents false,
   `getStartWatchResourceVersion` calls it on `ctxRL` before `createWatchChan`). Say that the strict
   control covers only RV > 0 with a fake watcher, and cite the reviewer's real-member recording test
   `/shared/tmp/coord-81/k8s7f5-review/clientkeys/keys_test.go` (or extend the control).
5. Rebuild (targeted, then the full build under flock and the cap), `etc/tcb-report.py --check
   --update` (one new axiom expected, `k8sfeature.featureOn_persistent`; report if it changes), the
   collections (`--collection etc/tcb-collections/k8setcd3.txt --check --update`; check all 55: the
   loop must not be cut by `head`), gates. Add an "S1 review" section to the freeze note (each finding,
   the fix). Add a STATUS entry (oldest moved to status-history's list, append only, `wc -l` check),
   noting the temporary premise of Q6 is not yet introduced (7f-5a). Merge lean, land via
   `etc/land.sh` on 81's go, report.

## Next, in order
1. DONE (`23af282dca`): S1 built (full build passes), checks in `notes/k8s-7f5-freeze.md` "Checks"
   (tcb: NEW `k8sfeature.featureOn_persistent`, also in collection k8setcd3; not updated). STOPPED for
   81's axiom review of S1.
2. After the review: apply its fixes; `etc/tcb-report.py --check --update` and the k8setcd3
   collection's `--update`; STATUS entry; merge lean; land S1 via etc/land.sh (81's go). Then 7f-3a statements (with T5-a's translation: the dry-run
   patch `/shared/tmp/k8s7f5/goose-dry-full.patch` has the client/metadata toml lines), STOP (S2).
3. 7f-3b/3c, and 7f-5a's Draft in parallel (Q1), STOP (S3) at the Draft.
4. Left from S0: the many-watches check (Scope §5: `isClientWatcher` persistent, repeated `Watch`).

## Pitfalls
- Every trusted text over a context must state every `ctx.Value` key the modelled code reads,
  and the methods called on what it returns (APF's `Signal()`: `apf_context.go:50-51`).
- `prevKv` none is reachable without compaction (`issues/etcd-watch-prevkv-before-created.md`): the
  client spec must admit it.
- `watchGRPCStream.run` (3368 lines): check with `etc/lean-check.py --fast --split`.
- The etcd fork's sources at the pin `0b50f0426` are in the module cache
  (`~/go/pkg/mod/github.com/upamanyus/etcd/{client,server,api}/v3@v3.0.0-20261112123031-0b50f04262d9`);
  `.lake/go-src/etcd` is at another revision.

## Build
Every lake command with `--packages=/shared/tmp/manifest-ddc.json` (scripts: `LAKE_OPTS=...`), under
`systemd-run --scope -q -p MemoryMax=64G`; full builds also under `flock /shared/tmp/etcd-grove-build.lock`.
Go tests under `systemd-run --scope -q -p MemoryMax=32G`, `GOWORK=off`, `PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`.
This worktree's `.lake/build` state: as 7f-4 left it; check `df -h /shared` before any seeding (ask 81).
