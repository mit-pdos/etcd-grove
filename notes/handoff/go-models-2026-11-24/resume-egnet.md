# egnet (S6) resume notes

## Decisions (lead)
- D1 approved: Go's `conn`/`TCPConn`/`TCPListener`/`netFD` types and their methods translated. The models sit at the netFD methods, the sockopt functions, `TCPListener.accept`/`close`, `Listen`, `Dial`, `DialTimeout` and `TCPAddr.String`. Proofs are ported layer by layer.
- **D2 decided by Upamanyu: verify the real code.**
  - Translate Go's real `OpError.Error`/`Timeout`/`Temporary`, `isConnError`, the `timeout`/`temporary` interfaces, and anything else plain-Go in net.go's error types.
  - Delete their Lean models (and `model.errFlag`, `model.OpError`, `model.timeoutError`) from `Net/TrustedCode/net.lean`, and the three names from `trusted` in `Net/Code/net.toml`.
  - Specs `OpError.Timeout.spec`, `OpError.Temporary.spec` and the lemma `wp_OpError_Error` gain the precondition: `Err` is one of net's own errors (`closedErr`, `ed` = `poll.ErrDeadlineExceeded`'s value, a `*timeoutError`, a `sysErr`), and `Source`/`Addr` are nil or `netAddr`.
  - The 5 callers discharge it: `Net/Proof/net/http/connReader__backgroundRead.lean`, `Net/Proof/net/http/Results.lean`, the 3 sites in `Net/Proof/net/rpc/Errs.lean`, and `Dsverify/Proof/raxos/Proxy/NetAcceptLib.lean`.
  - No top-level theorem changes.
  - In the packet, list each spec before/after, marked "precondition approved by Upamanyu".
  - The callees the real code reaches need translation: `internal/poll`'s `errNetClosing.{Error,Timeout,Temporary}` and `DeadlineExceededError.{Error,Timeout,Temporary}` (`Code/internal/poll.toml`), `os.SyscallError.Error` (`Code/os.toml`), and `syscall.Errno.{Timeout,Temporary}` (`Code/syscall.toml`; `Errno.Error` stays trusted, arbitrary). Put those translate-list additions in their own commit and send the hash to the lead (who tells egos).
  - Specs for them: any string; the constant flags.
  - `TCPAddr.String` stays the model (an arbitrary string).
- No temporary empty `FieldAssumptions` class.
- netgo approved: every project is translated with `-tags netgo` (S0's splicer refuses cgo packages). Commit `b68f8335b8` (etc/goose.py `BUILD_TAGS`) is on `go-models-rest/2026-11-24`, pushed. Still owed: `goose.py --check` of every project, showing no change but net's.
- Shared infra belongs to egrest: `internal/gomodel` config `6bfc699d3f`, and goose built from `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/pgmR-xtools` (x/tools v0.51), see `gmr-egrest/goose-howto.md`. Do not write a gomodel config. In the shared worktree eg-gmr, every goose.py run goes through `flock /home/ubuntu/.claude-E/jobs/b20ef685/tmp/eg-gmr-goose.lock`.
- I may add `Code/internal/poll.toml` and `os`/`syscall` translate-list entries in a separate commit, then send the hash to the lead.

## State
- My own worktree: `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/eg-gmr-net`, branch `go-models-rest-egnet/2026-11-24` off `b68f8335b8`. It is separate because a regenerated net breaks every Net proof, and the shared worktree eg-gmr is used by egos/egrest; my files there were restored to HEAD.
- Committed and pushed as WIP `6bddc60db8` on `go-models-rest-egnet/2026-11-24` (does not build past GeneratedProof: the proofs still use the old layouts):
  - `models/net/model.go`: the Go model. Stubs `ext*`, `closedErr`, `stuck`; the extension id is in `netFD.pfd.Sysfd`.
  - `Net/Code/net.toml`: new header, translate list, trusted stubs plus `errClosed` and the 3 OpError methods, `[model]`, `[[skip]]` of the vars and of 4 blanks `_@lookup.go:283`, `_@net.go:609/843/844`.
  - `Net/TrustedCode/net.lean`: the stubs' `.impl`, OpError models, `errClosed.init`.
  - `Net/ManualProof/net.lean`: now empty.
  - Regenerated `Net/{Code,GeneratedProof}/net.lean`.
  - KvNet copies, from `copy-part.py --part KvNet` with `PERENNIAL_DIR=/home/ubuntu/.claude-E/jobs/b20ef685/tmp/eg-tri-perennial2` (a checkout at pin 580868e54; read only).
- Build of `Net.GeneratedProof.net KvNet.GeneratedProof.net` on the VM: log `gmr-egnet/build1.log`.

## Commands (from eg-gmr-net)
- Regenerate: `PATH=/home/ubuntu/sdk/go1.27.3/bin:$PATH GOTOOLCHAIN=local python3 etc/goose.py --perennial /home/ubuntu/.claude-E/jobs/b20ef685/tmp/pgmR-xtools --project net`
- KvNet copies: `PERENNIAL_DIR=/home/ubuntu/.claude-E/jobs/b20ef685/tmp/eg-tri-perennial2 python3 etc/copy-part.py --part KvNet`
- Build: `/shared/tmp/vm/vmlake build <modules>` (2 VM slots shared; run in background).
- Trial goose directly: `gmr-egnet/gopath/bin/goose -tags netgo ...` (x/tools 0.51 build; see the plan for the args).

## Next steps
1. Fix any elaboration errors in `Net/TrustedCode/net.lean`, `Code/net`, `GeneratedProof/net`. Likely spots: the stub `.impl` names and arity; the `internal.gomodel.Stuck.impl` import path; the arguments of `ExternalOp` `Write`/`SetDeadline`/`SetSockopt` matching `Impl.lean`'s table: `Write (#e,(#bs,#first))`, `SetSockopt (#e,(#kind,#x))`. A `SetSockopt` x is an int64 here (the Lean passed `#(W64 0)` / `d`).
2. Specs (statements unchanged):
   - In `Net/Proof/net/Base.lean`, `connAt t cn s a la ra` becomes `∃ nw fd, tcpNet nw ∗ t ↦□ TCPConn.mk (conn.mk fd) ∗ fd ↦□ netFD.mk (FD with Sysfd = endId cn s, rest zero) 0 0 false nw la ra ∗ netAddr la ∗ netAddr ra ∗ netConnAt`.
   - `lisAt t l x`: `t ↦□ TCPListener.mk fd zero-ListenConfig ∗ fd ↦□ netFD.mk (Sysfd = l) … nw x nil ∗ netAddr x ∗ ⌜l ≠ 0⌝`.
   - Check how `endId` (w64) relates to `Sysfd : int` (w64). Drop `field_sem`, `model.*_ty_eq` for removed `model.*` names (model.conn, TCPConn, TCPListener, Conn, Listener, TCPAddr, IP, Addr, Errno are gone from TrustedCode; only model.OpError, model.timeoutError remain).
3. New `Net/Proof/net/FD.lean` (defs tier):
   - one WP lemma per model: `netFD.{Read,Write,Close,closeWrite,Set*Deadline,accept}`, the six sockopt functions, `TCPListener.accept`/`close`;
   - one per helper: `kindErr`, `codeErr`, `anyTCPAddr`, `modelFD`, `newConn`, `netOk`;
   - one per stub: `ext*` (from `GooseLang/Ext/Net/Specs.lean`'s `wp_net_*`), `closedErr`.
   Then re-prove the 30 `Net/Proof/net/*.lean`, plus `Errors.lean`, `Init.lean` (skipped vars: simpler) and `AtAddr.lean`, over the real wrappers. Proofs that unfold `connAt` elsewhere: `Dsverify/Proof/.../swiftpaxos/lib/NetConn.lean`, `swiftpaxos_epaxos/replica/ClientListener.lean`, and the KvNet copies (regenerated by copy-part).
4. Remove `[net.FieldAssumptions]` / `[field_sem : net.FieldAssumptions]` from 546 files (Net 234, Dsverify 173, KvNet 69 via copy-part, main `Proof` 61, `Spec` 5, `etc/kitlibs-check-test` 4), and from the generators `etc/gen-link.py`, `etc/link_walfs.py`, `etc/link_bbolt.py`, `etc/dsv/{kitgen,paxos,rabia,swiftpaxos}.py`, `.claude/skills/dsverify/NET.md`. Rerun the generators' `--check`.
5. Evidence:
   - `go vet`/`go build -overlay $(goose model-overlay)` of `examples/net` with `-tags netgo`, and `go test -overlay … -tags netgo net -run 'TCP|Dial|Listen|ZeroValues|CloseTwice'`. The stub bodies are plain blocking sockets: list the tests left out.
   - `etc/model-tests.sh` lines (egrest's script) for net, sent to the lead.
   - `goose.py --check` for all projects, through the flock in eg-gmr or here.
6. `tcb-report.py --collection` (net, kvnet, models-net, dsv kits) before (origin/lean build) and after; `#print axioms` of the touched results; the review-trusted skill in fix mode; `gmr-egnet/packet.md` in S1's format; the netgo claim stated in `Net/Code/net.toml` (already in goose.py).

## Later lead notes
- egrest infra at `9dac1834d6` on go-models-rest/2026-11-24:
  - `tcb-report.py` has a "Go models" item (automatic).
  - `etc/model-tests.sh` (= `etc/gomodels.py test`) has a TESTS table. Append net's rows: name, config dir `Net/Code`, `project:net`, overlay packages, go test args (`-tags netgo`), what is left out and why.
  - Run: `PATH=/home/ubuntu/sdk/go1.27.3/bin:$PATH etc/model-tests.sh --perennial /home/ubuntu/.claude-E/jobs/b20ef685/tmp/pgmR-xtools net`.
  - Merge 9dac1834d6 into my branch first.
- Check whether a net model changes which functions a package-variable initializer reaches, so that init order would differ from the real program's (as egrest found in crc32). Report in the packet either way.
  - Model functions reference `errTimeout`, `poll.ErrDeadlineExceeded` and `io.EOF`. No real initializer calls `Dial`/`Listen`/netFD methods, I believe, but check with `go vet`-level reasoning or `-gcflags`, or compare the init order goose emits with Go's (`go build -ldflags` / `GODEBUG=inittrace=1`).
- goose-model-overlay-rest-xtools moved to 78d6ef937 (runtime push-linkname drop, CheckAPI ignores param names); the VM is saturated: read the Update section of gmr-brief.md, batch vmlake targets.

## Session 2 (respawn, 2026-11-24)
- Merged origin/go-models-rest/2026-11-24 (14aa39bd7f) into the branch (3cfbfd4b6f).
- 7979b955cc: Code/internal/poll.toml (errNetClosing/DeadlineExceededError methods) and Code/syscall.toml
  (Errno.Timeout/Temporary, EINTR EMFILE ENFILE ETIMEDOUT ECONNRESET ECONNABORTED), bboltfs regenerated
  (Code/os.lean churn from egos's in-flux model restored to HEAD). Hash for the lead/egos.
- 47389d21ab (WIP): D2 applied in net.toml (OpError.Error/Timeout/Temporary, isConnError, timeout,
  temporary translated), OpError Lean models deleted; detach without runtime.SetFinalizer (the first
  build failed on `_root_.Perennial.runtime.SetFinalizer`); net+kvnet regenerated; KvNet recopied with
  PERENNIAL_DIR=/home/ubuntu/.claude-E/jobs/b20ef685/tmp/eg-net-perennial (detached worktree at 580868e54).
- Build of Net/KvNet GeneratedProof.net + GeneratedProof.{syscall,internal.poll}: gmr-egnet/build2.log.
- STOPPED (reported to lead): Go's conn.Read compares the error with io.EOF (`err != io.EOF`):
  GooseLang's interface equality runs CheckComparable on equal dynamic types, and a closed/timeout
  error equal to io.EOF would go unwrapped. Conn.Read.spec/specLc only take `globalAddr io.EOF ↦□ eof`
  and `globalAddr ErrDeadlineExceeded ↦□ ed` (arbitrary values): a new premise is needed (eof an
  `*errors.errorString`, e.g. `isPkgInit io`; ed a `*poll.DeadlineExceededError`, poll's PkgInit fact
  strengthened). Waiting for the lead's decision.
- build2 (Net/KvNet GeneratedProof.net, GeneratedProof.{syscall,internal.poll}) on 47389d21ab: OK (lake exit 0).

## Session 3 (2026-11-24, after the lead's decisions; head 92a6aa850a)
Decisions in force: D2 OpError precondition `opErrOk v` (Base.lean) on OpError.Timeout/Temporary specs
(done) and on wp_OpError_Error (to write); Conn.Read/specLc take `isPkgInit io ∗ isPkgInit internal.poll`,
Conn.Write `isPkgInit internal.poll` (commit 629cc5c8b2, own commit, lead-decided). Port the ~60 clients
(list: `git grep -ln "Conn\.Read\.spec\|Conn\.Read\.specLc\|Conn\.Write\.spec"`); NO top-level theorem
may gain a premise (if one would, stop and report the chain to the lead).
Commits: 9b0ef54c04 poll fact strengthened (+ errDeadlineExceeded_of_pkgInit); 53e84fb6e8 merge of main
(pin b3f2fc485; Perennial checkout at the pin for copy-part/gen-init: PERENNIAL_DIR=.../tmp/puplus, read
only); FieldAssumptions removed from 549 files + generators (gen-link.py list entry, dsv/*.py, kitgen,
NET.md) + 13 TopLevelRobustness intros; Net/ManualProof/net.lean KEPT (empty): GeneratedProof imports it.
Go model helpers renamed: kindErr→codeKindErr, closedErr→netClosingErr (trusted stub; TrustedCode and
toml updated); net regenerated (KvNet Code needs copy-part + `goose.py --project kvnet` at the end).
gen-init: the full run fails (KeyError internal.filepathlite, egos's in-flux); per-package `gen-init.py os`
works; I patched os Init copies by text substitution.
Proof state: Base.lean rewritten (fdAt/connFd/lisFd/connAt/lisAt, edAt, resKind, kindErr_ne_nil,
netOwnErr/addrOrNil/opErrOk, edTyped, kindErr_netOwnErr, opErr_opErrOk). Errors.lean rewritten as a pilot
(stubs, closedErr, kindErr, codeErr, anyTCPAddr, netOk, modelFD, newConn; wp_conn_ok and wp_fd_Close end
in `trace_state; sorry` to learn the goal shapes). Pilot proofs: Conn__Close (trace/sorry),
Conn__LocalAddr, Conn__RemoteAddr, TCPListener__Addr. Old Errors.lean saved in gmr-egnet/Errors.old.lean
(wp_OpError_Error, wp_errFlag shapes). build6.log = the pilot build (Base fixed: `show` for kindErr's
match). Everything else in Net/Proof/net/*.lean still has old model proofs.
Next: read build6's trace_state goals; write wp_conn_ok, wp_TCPListener_ok, the netFD lemmas
(Close, closeWrite, Set*Deadline, sockopts via setX functions, Read, Write loop, accept), TCPListener
accept/close; then wrappers by template (gen script idea: one template for the Close-like ops); then
OpError Error/Timeout/Temporary over real Go (callees: errNetClosing/DeadlineExceeded/timeoutError
methods, os.SyscallError.Error, Errno.Error via Proof/syscall/ErrorOk errno_stringMethodSpec,
TCPAddr.String model = extAnyString); Init.lean (gen-init NET_SPECIAL: closedErr now Go fn name
netClosingErr irrelevant; errClosed stays trusted init); clients; copy-part; builds; tcb-report.
Model tests: `etc/gomodels.py test net` (TMPDIR/GOTMPDIR under gmr-egnet/tmp): 6 example packages pass.
goose.py --check: all up to date except bboltfs Code/os.lean (egos's).

## Learned from build6 (pilot; head a3218fa167)
- After `wp_func_call; wp_call` the pure part often already reaches the post: use `(try wp_auto)`.
- `if: #(decide (c = W64 0))` stays symbolic: `rw [decide_eq_false hk]` (codeErr), `rw [show (!decide (c = null)) = true by simp [hc]]` (conn.ok; c ≠ null from typedPointsto_not_null of the conn field points-to).
- wp_auto performs the let-bound `GoAlloc` of a composite literal itself (modelFD: goal becomes `Φ #«$r0_ptr»`), so do not `wp_alloc`; find the hypothesis name (likely `«$r0»`) and `ipersist` it. kindErr's anonymous `&SyscallError{…}` and anyTCPAddr's `&TCPAddr{…}`: check the same (errors at Errors.lean ~127/174/193 were codeErr's decide, modelFD's alloc, newConn's first wp_auto "no progress": start newConn with wp_apply directly).
- netFD methods: wp_auto stops at the nested load `![go.int] #fd.[netFD,"pfd"].[FD,"Sysfd"]` from `fd ↦□ v`: `iStructNamed` Hv then the `pfd` field (nested) to load Sysfd; then the stub call `((FuncResolve extClose []) #()) id`: write Φ-style stub lemmas (`WP (App (Val (@! net.extClose)) (Val #id))`) and `wp_apply` them.
- Conn wrappers: after wp_method_call the promoted method becomes conn's; `iStructNamed Ht2` names the field points-to `conn` (c ↦□ {fd' := fd}).

## Session 4 (2026-11-24, head 763a42430b, pushed)
Done (all check with `etc/lean-check.py --fast -a` locally; no full lake build yet, VM was down):
- Errors.lean: stub lemmas (`wp_extClose/CloseWrite/SetDeadline/SetSockopt/LisClose/Read/Write/Listen/Dial/Accept`,
  each takes the spec-form AU and returns `Q res` + `res ≠ timeout`), `wp_codeErr_nt`, `fdAt_elim`, `lisAt_elim`,
  `wp_conn_ok`, `wp_TCPConn_ok`, `wp_TCPListener_ok`, netFD lemmas `wp_fd_{Close,closeWrite,Set*Deadline,Read,Write,accept}`,
  `wp_set{ReadBuffer,WriteBuffer,KeepAlive,Linger,NoDelay,KeepAliveIdle}`, `wp_TCPListener_{close,accept}`, `fdReadErr`.
- Net/Code/net.toml: `TCPConn.ok` added to the translate list (goose emits the promoted MethodUnfold only for listed
  promotions; Go's TCPConn methods call `c.ok()` on *TCPConn). net regenerated (Net/Code/net.lean +3 lines).
  KvNet/Code/net.toml + copy NOT yet updated (copy-part step).
- Every Net/Proof/net/*.lean wrapper re-proved over the real Go except: OpError__Temporary's sys (Errno) branch = sorry.
  Problem: inside Errno.Temporary, `e.Timeout()` is `MethodResolve syscall.Errno.ty "Timeout" #n` applied; wp_auto stops,
  wp_apply of a `methods`-form lemma does not match (instances ↓u/NotInterface ARE found). Try: a lemma stated over
  `App (App (Val (GoInstruction (MethodResolve Errno.ty go!"Timeout"))) (Val #n)) (Val #())`, or wp_bind + the
  PureWp of go_method_resolve_step.
- Patterns learned: wp_start pulls `isPkgInit` premises into Hpkg, Hpkg2 (not in the pattern); TCPConn's own methods
  are already unfolded by wp_start (so `(try wp_method_call)`); `unfold f` also unfolds hyps (use *_elim lemmas);
  Φ-goals after a let-bound alloc: `iapply wp_fupd` first, then `ipersist «$r0»; imodintro`; `match` on a constructor
  in an Iris hyp: `dsimp only`; GoType inequalities: `simp only [goose_wp_simp_extra] at h`; interface assertion:
  `rw [show go.typeSetContains T I = true by go_type_set]`; `resKind (some k)` → `rw [show resKind .. = kindErr .. from rfl]`.
Not done (in order): wp_OpError_Error with `opErrOk` (old shape in gmr-egnet/Errors.old.lean; real Go needs
`Err.Error()` per netOwnErr kind, `os.SyscallError.Error`, Errno.Error via errno_stringMethodSpec, Addr.String model),
its 5 callers; Init.lean (Net/Proof/syscall/Init.lean on the shared branch imports both Proof.runtime.PkgInitExt and
Net.Proof.runtime.PkgInitExt via Proof.internal.gomodel.Init: gen-init needs `internal.gomodel` in NET_MAIN/redirect —
same bug on origin/go-models-rest; tell the lead); ConnIo.lean, http/rpc/textproto and the ~60 Read/Write clients
(isPkgInit io/poll); KvNet copy-part + goose kvnet; builds; tcb-report; packet.

## Session 5 (2026-11-24, head 7d5bebaf64, pushed)
Builds: VM only for anything beyond 1-2 files (Upamanyu 15:30Z); locally only etc/lean-check.py on one file. VM down: wait.
Done (lean-check --fast -a, 0 errors, no sorry):
- 6a177b9634 OpError__Temporary: Errno branch proved. Key trick: `haveI : go.NotInterface go.uintptr :=
  ⟨by simp [go.uintptr]⟩` (Perennial has no instance for the predeclared named types; Errno's underlying is
  go.uintptr, so MethodResolve Errno.ty never stepped). Also `iStructNamed` of the SyscallError points-to.
  (Perennial gap worth a notes/perennial-changes.md line: NotInterface instances for predeclared types.)
- 7d5bebaf64 new Net/Proof/net/OpErrorMsg.lean: opErrMsg/opErrMsg_ne (moved here), opPrefix lemmas,
  `errStr e` (∃ ii, e = ok ii ∗ fmt.stringMethodSpec ii "Error"), netOwnErr_errStr, `opErrMsgOk v`
  (errStr Err ∗ addrOrNil Source ∗ addrOrNil Addr; weaker than opErrOk), opErrOk_opErrMsgOk,
  `wp_OpError_Error pe v Φ : pe ↦□ v -∗ opErrMsgOk v -∗ ▷(∀ msg, ⌜opErrMsg v.Op' msg⌝ -∗ Φ #msg) -∗ WP ...`.
  rpc/Errs.lean and Dsverify NetAcceptLib.lean now import it (they do not compile yet).
OPEN (the callers' precondition; decide, then do):
- rpc/Errs.lean: errNE_opErr, errAny_opErr (any src/addr/e), errSrv_resErr_read, errNE_resErr, errAny_resErr
  (arbitrary ed, src, addr) cannot give opErrMsgOk: resErr (some k) = ∃ e, opErr .. e err ∗ kindErr k ed nm e,
  and kindErr .timeout (some ed) says only e = ed (errStr needs edTyped ed), src/addr are free.
  Option A (recommended, clean): strengthen resErr's `some k` body with `errStr e ∗ addrOrNil src ∗ addrOrNil addr`
  (move errStr/addrOrNil to Base.lean; fmt.Args import). Producers: the 17 Net/Proof/net wrappers that build
  resErr (from kindErr + edTyped (Read has isPkgInit poll) and connAt/lisAt's netAddr la/ra). Then every
  consumer (97 files mention resErr, ~10 call errAny/errNE_resErr) is unchanged. A post strengthening only.
  Option B: premises (edTyped ed, addrOrNil src/addr) on errAny_resErr & co., discharged at ~12 call sites.
- errAny_opErrPtr ("any *OpError", DialHTTPPath.lean:427/452): needs errStr of Err. Site 452 (errors.New):
  from wp_errors_New' (Hx) directly. Site 427: Err = http.ReadResponse's error, whose spec says only
  err ≠ nil: needs ReadResponse.spec's post strengthened to errStr err, with a law that E's errors are errStr
  (DialHTTPPath discharges it from the conn's read errors = resErr → errStr under option A); and ReadResponse's
  proof (Net/Proof/net/http/ReadResponse.lean, 463 lines; bufio/textproto model errors) re-done. Untrusted,
  internal spec; no top-level premise.
Then: steps 3-7 of the prompt (merge go-models-rest for gen-init, Init.lean, ConnIo/http/rpc/textproto + ~60
Read/Write clients, KvNet copy-part + goose kvnet, VM builds, tcb-report, packet).

### Lead decision after session 5 (apply; do not reopen)
1. Option A: resErr (some k) body gains `errStr e ∗ addrOrNil src ∗ addrOrNil addr` (move errStr, its
   persistence instance and addrOrNil to Base.lean, which then imports Perennial's fmt Args); prove the
   extra facts in the 17 producing wrappers (kindErr + edTyped → netOwnErr_errStr; connAt/lisAt netAddr la/ra).
   Then the rpc/Errs lemmas get opErrMsgOk from resErr; errNE_opErr/errAny_opErr take opErrMsgOk-shaped facts.
2. DialHTTPPath:427: strengthen http.ReadResponse.spec's post to `errStr err` (with a law: E's errors are
   errStr), redo Net/Proof/net/http/ReadResponse.lean; DialHTTPPath discharges the law from resErr (option A).
   Site 452: errStr from wp_errors_New'.
3. PACKET NOTE (Perennial follow-up, not on this branch): no `go.NotInterface` instance for predeclared named
   types (go.uintptr etc.: `def uintptr := go.Named "uintptr" []`), so MethodResolve on an Errno value does not
   step; worked around by a local `haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩`
   (OpError__Temporary.lean, OpErrorMsg.lean; Perennial's own time/Duration proofs do the same for int64).
Then items 3-7. Rules: VM-first builds, lean-check one file at a time, ≤60% context, no sub-agents.

## Session 6 (2026-11-24, head 2617d83bd8, pushed; stopped by the lead's wrap-up)
Done (lean-check --fast -a, 0 errors):
- 3819c7432d Option A: Base.lean holds errStr and addrOrNil (imports Perennial.Proof.fmt.Args); resErr (some k) =
  ∃ e, opErr ∗ kindErr ∗ errStr e ∗ addrOrNil src ∗ addrOrNil addr. OpErrorMsg: resErr_intro (hnw, edTyped),
  addrOrNil_addr/nil. The 17 producing wrappers use it.
- 5650847a2b: rpc/Errs (errNE_opErr/errAny_opErr take errStr+addrOrNil; errAny_opErrPtr takes opErrMsgOk v;
  errSrv_resErr_read), Dsverify NetAcceptLib errAny_resErr' (edited, but unchecked: its cone imports ConnIo,
  which fails). badStringError.spec post + errMsgOk (proof done); http.ReadResponse.spec: new law premise
  `□ ∀ r err, E r err -∗ errMsgOk err`, post `⌜err ≠ nil⌝ ∗ errMsgOk err` (proof done); protocolError_msg,
  mimeErr_msg, errMsgOk_of_wp moved into http/RequestDefs. readRequestLimit checks.
- 2617d83bd8 (WIP): OpErrorMsg errStr_of_wp, resErr_errStr; HttpDefs crErr = Lb ∗ net.errStr err;
  DialHTTPPath: Hlaw3, sites 427/452 via errAny_opErrPtr + opErrMsgOk. DialHTTPPath errors to fix:
  (1) readErr_some' was inserted BEFORE readErr_some: move it after; (2) crStream's two wp_Read calls (lines
  ~183, ~253): Conn.Read.specLc now takes `isPkgInit internal.poll` too (step 4): crStream needs that premise
  (check whether DialHTTPPath.spec has it; if not, it is the Read-client port, no top-level premise allowed);
  (3) line ~382: `obtain ⟨Hw, -⟩ := Hw` breaks (the wp_Write post's `%Hw` naming): look at the goal.
Note: http's errMsgOk and net.errStr have identical bodies (follow-up: unify).
Next: fix DialHTTPPath, then steps 3-7 (merge go-models-rest + gen-init, ConnIo and ~60 Read/Write clients,
KvNet copy-part + goose kvnet, VM builds, tcb-report, packet). No VM build was started this session.

## Session 7 (2026-11-25, worktree ho-gmr, VM key c61dd42e08d7d686)
Decisions (recorded here; spec changes listed for the packet):
- `Errno.Error` is translated (reads syscall's `errors` table), so `errStr e` (Base.lean) is now
  conditional: `∃ ii, e = ok ii ∗ □ (syscall.errnoOk -∗ stringMethodSpec ii "Error")`. Producers
  (the 17 wrappers, resErr) need no package fact; consumers pass `syscall.errnoOk`:
  `wp_OpError_Error` (+ errnoOk arg), rpc/Errs `errNE_opErr`/`errAny_opErr`/`errAny_opErrPtr` (LHS ∗),
  `errNE_resErr`/`errAny_resErr`/`errSrv_resErr_read` (`errnoOk ⊢ resErr -∗ …`), rpc `inErr_read`,
  `rdErr_read(F/E)` (LHS gains errnoOk), http `readErr_msgOk` (LHS), Dsverify BufioNet
  `resErr_errOrNil`, NetAcceptLib `errAny_resErr'`, `readFull_errAny`. All Proof-level lemmas.
- `fdAt` (a netFD) carries `isPkgInit pkg_id.net`: `connAt_net/poll/io/errnoOk`, `lisAt_net/errnoOk`,
  `errnoOk_of_poll`, `edTyped_of_poll` (Base.lean). So Conn.Read/Write's lead-decided package premises
  are discharged from the connection (ConnIo laws keep their old statements; rpc/http/examples derive
  them), and errnoOk at every consumer. `wp_modelFD`/`wp_newConn` take `isPkgInit net`.
- Spec changes (premise `isPkgInit pkg_id.net` added, every caller derives it with solve_pkg_init /
  wp_apply's automatic package-fact discharge): `net.Dial.spec`, `net.DialTimeout.spec`,
  `net.Listen.spec`, `net.Listen.specAddrOk` (AtAddr), `net.rpc.Dial.spec`; Dsverify lab
  `net.Dial.labProof`, `net.Listen.labProof`, `net.Listen.labProofU` (NetLab.lean); main tree
  `EtcdGrove.net.Listen.spec` (Spec/net/Listen.lean). No top-level statement changed (to confirm
  with the full build: the etcd examples calling EtcdGrove net.Listen must find `isPkgInit net`).
- 53 Dial/Listen call sites patched by script (`tmp/egnet7/addnet.py`: `ihave #HnetPk … solve_pkg_init`
  + `(try iframe HnetPk)` in the call's first bullet).
- Other fixes: ConnReaderLemmas NewCond (pin's `isNotifyList`), backgroundRead's `OpError.Timeout`
  gets `opErrOk` (kindErr_netOwnErr + edTyped_of_poll), connReader__Read imports OpErrorMsg,
  NetConn/ClientListener `TCPAddr.String` over the Go model (`net.wp_extAnyString`), KitConf
  `wp_log_Println` over Perennial's `log.wp_Println` (`wp_start_folded`), rabia server Link uses
  `fmt.wp_Printf` (Perennial.Proof.fmt.Link), InvBbolt `structure FsCtx (GF : BundledGFunctors)`
  (the `include GF in` fix did not add the parameter), errStr_of_wp moved out of the netExt section.
- Merged origin/go-models-rest/2026-11-24 (re-pin 30102d8b2, Net log.Println removed); KvNet copies
  regenerated (PERENNIAL_DIR=…/wt/p-gm-rest).
Lesson: wp_apply discharges `isPkgInit` conjuncts itself when derivable from the context;
`iframe Hio` then fails ("cannot frame") — use `(try iframe X)`. iapply does not.
Open: Proof/os/OffEnd.lean:85 (egos's a2077383e1 made Seek past modelSeekMax stuck: `wp_endOff`'s
hbig branch now reaches `gomodel.Stuck`; needs `m.size + off ≤ seekMax` as a premise and its callers
(fileutil preallocExtendTrunc) to discharge it — egos/lead decision, not done here).
Full build 2 (`tmp/egnet7/full2.log`, before the second merge of main, which brings OffEnd's fix
659b2fff8b) exit 1; remaining errors (next session, in order):
- Net: http/ReadResponse.lean:388 `icases` of a non-persistent `mimeErr E merr ∗ ∃ rr, ownReader…`
  (mimeErr_errStr's premise: split the pair first, keep the reader).
- Dsverify swiftpaxos: NetConn.lean:90 and epaxos ClientListener.lean:49 (`rewrite` in
  `wp_method_call`/`unfold TCPAddr.String.impl`: look at the goal; NetConn's version compiled in
  build 1? no — use `wp_method_call; wp_call` or the OpErrorMsg-private `wp_TCPAddr_String` made
  public); BufioNet.lean:172/216 unsolved goals (the Read/Write pkg premises: add
  `(try iframe …)`/connAt_poll as in KitDeps); OrchSend.lean:45 `GF` unknown (addnet.py's
  `(PROP := IProp GF)` in a file whose GF is named otherwise: use that file's name, e.g. netDistGF);
  raxos quepaxanet Linked.lean:80 type mismatch (a kit lemma's new Println/Listen argument).
- Not net (newly reached now InvBbolt builds, or the re-pin): backend unsafeRange (curAt vs
  backend.curAt), backend__Close/newBackend parse errors at `,` (FsCtx binder syntax?), os
  Rename.lean:135 (`And.ok`), k8s clock RealClock__*/real*__Stop (Perennial time spec change at the
  re-pin), RaftWitness kvwitness Adequacy.lean:183, Proof/os/OffEnd (fixed on main, re-check).

## Session 8 (2026-11-25, worktree ho-gmr, VM key c61dd42e08d7d686)
Builds (logs in `tmp/egnet8/`): full1 (head d087fb0bd7) exit 1, 16 modules; full2 exit 1, 8; full3
(after commit 2) exit 1, ONE module: `Dsverify...swiftpaxos.swift.SyncTail`. probe4 (SyncTail's
`swift.wp_PrintlnT` stubbed locally, never committed, reverted) exit 0: every other default target,
including the 17 modules downstream of SyncTail and swiftnet TopLevelRobustness, builds.
OffEnd / fileutil preallocExtendTrunc: fixed by main's 659b2fff8b (no error).
Fixes (commits on this branch, see their messages): FsCtx rcases patterns (4 fields), empty `∀,`
binders, ReadResponse wp_MIME reader dropped, BufioNet connAt_poll, OrchSend/AwaitConf/ServeProof
netDistGF, TCPAddr.String after wp_start, quepaxanet/k8s clock over Perennial's time Link,
kvwitness pkgInitTable (+4 packages), mvccrand/mvccfull/putget TLR proof intros (binder counts of
the already-changed statements). No statement changed.
EtcdGrove.net.Listen.spec's `isPkgInit net`: its callers (cluster3 StartBridge/StartMember, etcdstart
NewMember/StartMemberAuth/Serve, restart(N)/auth3 newMember/startMember) `wp_apply wp_Listen ...`
inside a function whose spec has `isPkgInit <its package>`; the package imports net
(Code/.../cluster3.lean imports Net.Code.net), so wp_apply's package-fact discharge derives
`isPkgInit net`; no top-level premise (the TLRs build, full3/probe4).
BLOCKED (needs Perennial / lead): SyncTail `swift.wp_PrintlnT` — `log.Println` is now Perennial's Go
model (`if Choose { fmt.Fprintln(modelDiscard{}, v...) }`), whose spec needs `fmt.ArgsWf`
(`printArgOk`). HandleSyncProof:1318 prints `log.Println("FQ:", r.FQ, "SQ:", r.SQ)`
(swiftpaxos recovery.go:704): `SQ`/`FQ` may be a `replica.Quorum` (`map[int32]struct{}`), which
fmt's model does not follow (`visitKind`: `notModelled()` for non-int/string kinds; Go prints it
by reflection, reading the map). Options: (a) Perennial fmt model: visitKind follows a map whose
keys/values are int kinds/empty structs (reads it: the spec then needs the map's points-to, which
HandleSyncProof has from quorumIs), plus `printArgOk`/`ArgWf` case; (b) lead decision otherwise.
Do not weaken: no sorry. Next: decide (a), then prove wp_PrintlnT over `log.wp_Println`
(callers with ArgsWf already: NewLeaderProof 670-682, HandleSyncProof 1279-1342).
