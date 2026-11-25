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

## Session 9 (2026-11-25, successor; worktree `<handoff-pickup>/.lake/gm/egnet`, local branch
`gm-egnet-pickup` pushed to `go-models-rest-egnet/2026-11-24`, VM key c61dd42e08d7d686)
Why a nested worktree: this session's harness refuses git outside its own worktree, so `wt/ho-gmr` (which
holds the local `go-models-rest-egnet/2026-11-24`, now behind origin) was not used. Scratch also inside:
`<handoff-pickup>/.lake/gm/scratch` (gendev9.sh, count.sh, packet-head/tail.md); logs `tmp/gomodels/s9/`.
- egnet-full (head 55c465fab3, from scratch after the sync dir's eviction): EXIT 1, only SyncTail (as session 8).
- Adversarial reviews round 2 (fresh agents, code only; demos `tmp/gomodels/adv2-egos/`, `adv2-egnet/`):
  * egos: UNSOUND directory Seek(SEEK_CUR) after Readdirnames (Go ext4 2^63-1, model 0) -> FIXED d2fa9c8519:
    model Readdirnames stuck unless off == 0, sets off = -1; Seek SEEK_END stuck on a directory fd (Go: htree
    end 2^63-1, not the size; measured, `examples/osfs/semantics/model_os_dir_offset.go`, TestDirOffset).
    Spec changes (internal): os dir Open specs give `os.ownOff f 0`, Readdirnames dir specs take it,
    `fileutil.ReadDir.wp_core`'s `Fd : Loc → w64 → IProp`; Off/OffEnd SEEK_END call wp_osFdKind. NsSOk fix
    0639d7d158. Conditional UNSOUND durable-vs-os state (no proved program mixes them): recorded in the packet,
    Impl.lean sentence still to add (a docstring change rebuilds durable's importers). DOC zero-File comment fixed.
  * egnet: UNSOUND Listen's error Addr never had a nil IP (Go's ":p": &TCPAddr{IP: nil}) -> FIXED 62c7668c97
    (`anyListenAddr`, `wp_anyListenAddr`). Latent: StructFieldRef of nil (Perennial FIXME). DOC Impl.lean stale
    (not changed). Rest no divergence, criterion 14 ok.
- Criterion-14 audit: packet section; the one deviation is fmt's trusted Printf error type (*errors.errorString
  vs Go's *fs.PathError), as on lean.
- egnet-os1 (d2fa9c8519): every edited os/fileutil/WAL/walfs/WalTester/KvNet module built; failures only NsSOk
  (fixed 0639d7d158) and SyncTail. egnet-os2: wp_anyListenAddr (fixed 4527ef62a8). egnet-os3 (4527ef62a8): EXIT 1,
  only SyncTail.
- tcb-report before/after (same 8369 roots): 329/329 axioms, same names; 0 sorry; results 1129/1129; BUT
  runtime.opaqueInitsOk, runtime.initFuncsOk, internal.runtime.sys.opaqueInitsOk now reach 81 roots (11 before):
  30 top-level results gain them, incl. RaftNoAx raft_kvdurable_porcupine_robust 0 -> 3 (os imports runtime:
  KeepAlive, Cleanup). For Upamanyu/lead (packet head + Evidence); not fixed.
- `etc/model-tests.sh --perennial p-gm-rest` with both fixes: tests ok.
- tcb-report: base = lean merge-base 622264bf5e built in its own sync dir (key 114ec12addaddd71, worktree
  `<handoff-pickup>/.lake/gm/base`, detached); both runs with the 3 SyncTail-dependent root modules excluded by
  a VM-side temporary patch of `etc/proof_roots.py` (`TCB_EXCLUDE` regex in `root_modules`, reverted after
  the run; not committed). Outputs `tmp/gomodels/s9/tcb-{base,egnet}.txt`.
- Packet: `notes/handoff/go-models-2026-11-24/packet-rest.md` assembled (head + dev diffs + tail).
Next: Upamanyu's log.Println decision (then SyncTail; drop the exclusion), his review of the packet.

## Session 10 (2026-11-25, successor; same nested worktree `<handoff-pickup>/.lake/gm/egnet`, branch
`gm-egnet-pickup` -> `go-models-rest-egnet/2026-11-24`; Perennial: nested clone `<handoff-pickup>/.lake/gm/perennial`
(branch goose-model-overlay-rest, ssh remote), since the harness refuses git in `wt/p-gm-rest`)
Coordinator decisions applied (etcd-grove#8 7153952113, 7166757537):
- (1) log.Println/Printf trusted EXACTLY as on lean: Perennial d81d2bfd8 (log's Code/GeneratedProof/Proof/Spec/
  TrustedCode/toml = lean's, verified by `git diff origin/lean` empty after regen; goose/model/overlay/log deleted;
  fmt's doPrintln model + fmt.Fprintln kept). model-tests pass (new skip: syscall TestDeathSignalSetuid, child
  prints with fmt.Println). etcd-grove c617de6bf3: re-pin + revert 49d90e1098 + KitConf wp_log_Println back.
- (2) runtime init: (a) NOT cheap (94 names-only runtime var initializers + 9 init funcs: findfunc/
  funcMaxSPDelta, cpu flags, lockInit, `go forcegchelper()`, unsafe.Sizeof checks; basic slice's runtime models
  cover none of it). (b) done as 4313327873: os.toml drops `runtime` from imports and leaves rawConn.Control/
  Read/Write names-only (the only translated os code calling runtime.KeepAlive; they call poll.FD.Raw*,
  names-only, so no proof passes them); no model text, no trusted text (lean had them trusted-panicking).
  gen-init PART_INITS/NET_MAIN lose runtime/atomic/sys; parts' runtime Init copies deleted.
- log gap analysis (issue text in packet-rest.md, "log.Println gap"): no proved path passes a Stringer/error.
Scratch/logs: `tmp/gomodels/s10/` (manifest-p10.json, genlink-all.sh pointing at the nested Perennial clone).
- Review of (b) (fresh agent): no divergence; DOC kvwitness pkgInitTable fixed (cde-era commit after 4313327873).
  Packet updated (decisions, "The `log.Println` gap" section = the issue text, review).
- NOT DONE (VM 146.148.67.74 unreachable from ~14:50Z to 16:05Z at least): 
  1. Perennial build of d81d2bfd8 (only log changed): from `<handoff-pickup>/.lake/gm/perennial`,
     `bash tmp/gomodels/scripts/fullbuild.sh <that dir> 9514b93e0b000028 tmp/gomodels/s10/int-full8.log`
     (incremental in pgmRest's sync dir; p-gm-rest is not used by anyone else).
  2. etcd-grove default build at the egnet head, key c61dd42e08d7d686 (`VMLAKE_KEY=c61dd42e08d7d686
     ~/vmlake/vmlake build` from this worktree): expect no failures (SyncTail back on the no-op model; os
     without runtime). Watch: kvwitness Adequacy table, os Init renumbering, io CopyFiles/CopyFrom.
  3. tcb-report after (`vmlake env python3 etc/tcb-report.py -o ...`, no TCB_EXCLUDE patch now) vs before
     (lean 622264bf5e, key 114ec12addaddd71, `tmp/gomodels/s9/tcb-base.txt` was produced WITH the 3-module
     exclusion: rerun base without it in its own sync dir). Expected: runtime axioms back at 11 roots, the 30
     results at lean's sets, `raft_kvdurable_porcupine_robust` 0 axioms; `--collection etc/tcb-collections/
     raft-noax.txt --check`. Then fill packet-rest.md "Evidence".
- (later, VM back at 146.148.67.74 after spot preemption; base sync dir evicted, rebuilt) RESULTS: Perennial
  d81d2bfd8 full build EXIT 0 (int-full10 + chunk 01 re-run int-full10b). etcd-grove egnet 16e82ffff7 default
  build EXIT 0, 28094 jobs (eg-full12; first attempt failed on a half-synced dir after the preemption).
  Base 622264bf5e (key 114ec12addaddd71, rebuilt, worktree `<handoff-pickup>/.lake/gm/base`) EXIT 0.
  tcb-report before/after, no exclusion: identical (8399 roots, 1119 results with the same axiom counts, 329
  axioms with the same root counts, runtime axioms 11/11, 0 sorry); raft-noax collection --check matches (0/0).
  Packet Evidence filled. Comparison script: `<handoff-pickup>/.lake/gm/scratch/tcbcmp.py BASE AFTER`.
Next: Upamanyu's review of the packet (coordinator brings it); once the basic slice lands on Perennial lean,
merge lean into goose-model-overlay-rest and shrink the packet.

## Session 10b (2026-11-25): basic slice landed (Perennial lean = d5eb93cb5). Plan (coordinator):
1. Perennial: merge origin/lean into goose-model-overlay-rest (overlaps: take lean's = landed basic slice),
   regenerate (pregen.sh --std-lib --models; restore strconv.lean churn), gen-link, model-tests, VM build of
   changed modules (or fullbuild.sh, key 9514b93e0b000028).
2. etcd-grove egnet: re-pin to the new integration head, merge etcd-grove origin/lean, regenerate (eggoose.sh,
   gen-init with PERENNIAL_DIR, copy-part, gen-raft-tla, gen-specs-pkginit, kitgen, s10/genlink-all.sh), default
   build (key c61dd42e08d7d686).
3. packet-rest.md: keep fmt/os/syscall/net/durable/crc32/go-token (+log note), drop sync/time/runtime/bytealg;
   recount MODEL: with Perennial's etc/model-deviations.py. tcb before/after only if axioms change.

## Session 11 (2026-11-25, same worktrees) — STATE
- Perennial `goose-model-overlay-rest` = **09bd3826c** (pushed): merge of lean d5eb93cb5 (basic slice landed).
  Conflicts: Code/syscall.toml ours (rest's prlimit1 model), etc/model-tests.sh ours (superset),
  goose/util/model.go + model_test.go lean's (the landed CheckAPI/sameSignature). Regen (pregen.sh --std-lib
  --models): no change but strconv churn (restored); gen-link no change; model-tests ok; `go test ./goose/...` ok.
  VM build: `tmp/gomodels/s10/int-full11.log` (fullbuild.sh, key 9514b93e0b000028) — check its chunk exits;
  re-run a chunk that exits 255/75 (connection loss) as in int-full10b.
- etcd-grove lean merge (1053 commits, 216 conflicts): PARKED on branch `go-models-rest-egnet-lmerge/2026-11-25`
  (8e07d6297f, pushed, WIP, does not build). Resolved by scratch/resolve3.py (diff3: our side only dropped
  FieldAssumptions -> lean's minus FA binders), resolve_intro.py (intro underscores), gen-init/gen-link by hand,
  generated files lean's (to regenerate). BLOCKER, left with diff3 markers: lean added UDP as trusted Lean
  (UDPConn, UdpFieldAssumptions, ListenUDP/WriteToUDP/ReadFromUDP, GooseLang/Ext/Udp, kvudp result) on the old
  trusted TCP net that egnet replaced by the Go-model net; plus KvNet renamed KvRaft on lean. Files with markers:
  Net/TrustedCode/net.lean, Net/ManualProof/net.lean, Net/Code/net.toml, KvRaft/Code/net.toml,
  Net/Code/go/token.toml, TopLevelRobustness of swiftnet/epaxosnet/quepaxanet (Proof+Spec), kvraft Spec,
  etcd dist/putget, k8s all. Needs a decision: UDP as a Go model (net.UDPConn over a UDP extension, a new
  MODEL item) vs keeping lean's trusted UDP beside the Go-model TCP (no new trusted text vs lean).
- egnet `go-models-rest-egnet/2026-11-24`: re-pinned to 09bd3826c WITHOUT the lean merge; regenerated (goose,
  gen-init, copy-part, raft-tla, specs-pkginit, kitgen: no change; gen-link-all running/`--write`). Next: commit,
  default build (key c61dd42e08d7d686, log s10/eg-full13.log).
- packet-rest.md shrunk: title/head (basic slice landed; log has no model), MODEL: table recounted with lean's
  etc/model-deviations.py: fmt 5, syscall(P) 1, os 19, syscall 9, durable 2, crc32 3, go/token 1, net 20 = 60;
  log diff section dropped. Head table rows still name d81d2bfd8/16e82ffff7: update after the build.
- tcb before/after: the pin bump changes no etcd-grove axiom (Perennial lean adds none); rerun only if the
  build's `#print axioms`/tcb differs.
- (Session 11 results) Perennial 09bd3826c full build EXIT 0 (int-full11, 4 chunks). egnet re-pinned
  (bedb8f9090): gen-link 0 differ, default build EXIT 0 (28094 jobs, eg-full13), `tcb-report --check` matches
  the baseline (329 axioms, 0 sorry): axioms unchanged, tcb before/after not rerun. Packet head updated.
  Open: etcd-grove lean merge (go-models-rest-egnet-lmerge/2026-11-25, blocked on lean's trusted UDP: decision).

## Session 12 (2026-11-25, successor) — the lean merge, UDP kept as lean's (etcd-grove#8 decision (a))
- Worktree `/home/ubuntu/.claude-D/jobs/43217da4/tmp/wt/eg-lmerge` on `go-models-rest-egnet-lmerge/2026-11-25`
  (VM key c61dd42e08d7d686, the egnet sync dir: the egnet worktree is idle). Scratch/logs: `tmp/gm12/`
  (scripts/strip_fa.py, goose*.log, full*.log).
- History: 8e07d6297f (the WIP tree, single-parent) + `4657f30f5d` = `merge -s ours 823cf434cc` (records the lean
  the WIP resolved) + `99e4f29144` = merge of egnet c8df216303 (notes only) + `2ce3866759` = merge of lean
  6865da10d6 (15 newer commits; one conflict, quepaxanet's intro line).
- UDP (decision (a), coordinator-E 7170869672): Net/TrustedCode/net.lean = our stubs + lean's UDP text verbatim
  (UDPConn struct/layout, UdpFieldAssumptions, UDP section) + the six definitions of lean's old trusted net the
  UDP section calls (`model.Addr/OpError/IP/Errno` type names, `model.opError`, `model.einval`), copied
  verbatim: no TCP model, no state, no extension op. ManualProof/net.lean = lean's UDPConn instances (+
  `Addr_ty_eq`/`Addr_named_underlying`, proved). net.toml: `UDPAddr` translated; `UDPConn`, `ListenUDP`,
  `UDPConn.WriteToUDP`, `UDPConn.ReadFromUDP` trusted. Regenerated `UDPConn.TypeAssumptions` = lean's
  (only the ReadFromUDP/WriteToUDP unfolds). GooseLang/Ext (Net, Udp, NetFsUdp) = lean's byte for byte.
- Condition 1 (no shared state): udpExt is its own extension ("net.udp"), own local/global state and ghost
  names (γsent, γsock); it reuses only pure definitions of the net extension (`addrOk`, `NetErr`, `errCode`,
  `failV`, Deploy's `addrSpace`), which egnet did not change. The UDP trusted section calls only
  `Udp.udpExt.name` operations. `UdpFieldAssumptions` is UDP's own class (the layout `uid/laddr/net`); no UDP
  file uses `net.FieldAssumptions` (gone with the Go-model net).
- FieldAssumptions: lean's newer files still had net/os.file/os.fileStat FieldAssumptions binders: stripped
  (294 files, `tmp/gm12/scripts/strip_fa.py`; docstrings restored by hand); `intro … fsem …` lines lose `fsem`.
- Deleted: files lean deleted that egnet had modified (KvNet/ remnants, part PkgInitExt copies, kvreconf's,
  PkgTables, RaftTla Init copies) and Net/Proof/internal/filepathlite/Init.lean (gen-init: stale).
- go/token.toml: lean's translated tokens/keywords/init.0 + our Go model of IsExported (no trusted).
- Regenerated with PERENNIAL_DIR = the nested Perennial clone (09bd3826c): eggoose.sh (net, models-net
  changed), gen-init, copy-part, gen-raft-tla, gen-specs-pkginit, kitgen, rpcdriver-boottable, k8s-deep,
  pbschema, genlink-all (0 differ); every --check passes.
- Coordinator (#8 7171395756): the six helpers kept, marked "UDP-only, retired by #58" (trailing comments, no
  line shifts); condition 1 accepted. packet-rest.md lists the 141 results/specs (+ 24 section-variable
  files) whose statements lose FieldAssumptions premises (`tmp/gm12/scripts/fa_results.py`).
- Full default build 1 (`tmp/gm12/full1.log`, at 2ce3866759): EXIT 1, 22 failing modules. Cause: lean's NEW
  code (since 622264bf5e) written over the old trusted net/os models; it needs the same port egnet S5/S6 did:
  * fixed (b873b7bcfb, building `tmp/gm12/b2.log`): dist TopLevelRobustness and mvccrand/mvccfull MainAt
    intro arities; Net go/token Init (`internal.gomodel.initialize'` first); `net.Listen.specHttp` (lean's)
    takes `isPkgInit net` like egnet's `net.Listen.spec` (5 callers: `ihave … · iPkgInit`); epaxos
    `DialHTTP_kit` / swiftpaxos `DialHTTP_tcp` take `isPkgInit net` (6 callers, `solve_pkg_init`), rpcdriver
    dial; Proof/net/ErrOrNil: `resErr_errOrNil` takes `syscall.errnoOk` (`opErr_errOrNil` deleted: unprovable
    without the Err's facts), callers via `net.connAt_errnoOk`; vr: `network.resErr_errOrNil` and
    `wp_debug_resErr` take `isPkgInit net` (`network.errnoOk_of_net`), `connAt_agree` over `connFd`/`fdAt`;
    stale KvRaft/Proof/net/OpErrorMsg (a KvNet copy header) recopied.
  * NOT fixed yet: gryff (`Lib/NetAddr.lean` wp_TCPAddr_String: use Net's, make OpErrorMsg's public;
    `N/ConnErr.lean` opErrPtr_errAny needs `opErrMsgOk v ∗ syscall.errnoOk`, cascading to resErr_errAny',
    resErr_errAny, rdErr_conn and 5 callers: thread errnoOk, e.g. from `isPkgInit net` via
    `network`-style errnoOk_of_net); Proof/os/LstatAnyS (lean-new, over `os.model.stat`: port to the os Go
    model, cf. egnet's Lstat proofs); Proof/encoding/json/NetInit (isPkgInitDef unify); Net/Proof/net/http/
    ServeLemmas (208, 378), InitFirst (89), Net/Proof/net/rpc/Client__CloseClosed (82: errnoOk wand);
    membership/OwnedMutex (Type mismatch: lean's change vs basic slice's sync.Mutex?). Then a full build to
    find what was behind them.
- STATE at hand-off point (session 12): branch `go-models-rest-egnet-lmerge/2026-11-25` pushed (head = this
  notes commit; code at b873b7bcfb). Targeted VM build of the fixed modules running: targets
  `tmp/gm12/targets2.txt`, log `tmp/gm12/b2.log` (key c61dd42e08d7d686). Full build 1 log `tmp/gm12/full1.log`.
- LEFT: (1) read b2.log, fix its failures; (2) port the not-yet-fixed modules listed above (gryff NetAddr/
  ConnErr cascade, LstatAnyS, encoding/json NetInit, http ServeLemmas/InitFirst, rpc Client__CloseClosed,
  membership OwnedMutex); (3) full default build (`VMLAKE_KEY=c61dd42e08d7d686 ~/vmlake/vmlake build`) until
  EXIT 0; (4) `vmlake env python3 etc/tcb-report.py --check`, then `--collection` kvraft, kvraft-udp,
  raft-noax `--check` (condition 2: kvraft-udp must stay 0 axioms/0 sorry = lean's); (5) condition 3: the
  build includes GooseLang.Ext.NetFsUdp.Adequacy and kvraft_udp TopLevelRobustness: confirm they built;
  (6) packet-rest.md head table (new head, build/tcb results) and note the spec changes this port adds
  (`net.Listen.specHttp`, `DialHTTP_kit`, `DialHTTP_tcp`, vr `wp_debug_resErr`/`network.resErr_errOrNil`,
  `net.resErr_errOrNil` gain `isPkgInit net`/`syscall.errnoOk` premises; `net.opErr_errOrNil` and
  `network.opErr_errOrNil` deleted) — these are lemma/spec premises, not top-level statements;
  (7) fast-forward `go-models-rest-egnet/2026-11-24` (`git push origin HEAD:go-models-rest-egnet/2026-11-24`
  from the lmerge worktree; the local branch is checked out in ho-gmr: don't touch it there); (8) #8 message.
- Targeted build b2 (`tmp/gm12/b2.log`, b873b7bcfb): EXIT 1, only NetInit, rpcdriver dial, vr Ghost left; fixed
  next: the old poll package-fact shape (`ErrDeadlineExceeded` an interface) → egnet's (`*DeadlineExceededError`)
  in NetInit, http/rpc InitFirst, gryff Client/Conn, N/ClientConn, N/WaitPeers; rpcdriver `dial.spec` and
  `Client.spec` take `isPkgInit net` (Main supplies it by `iPkgInit`); vr `wp_debug_resErr`: wp_start_folded
  consumes the isPkgInit conjuncts, net's fact re-obtained by solve_pkg_init. Full build 2 log `tmp/gm12/full2.log`.

## Session 13 (2026-11-25, successor) — the lean merge's port, continued
- Same worktree/key (`eg-lmerge`, c61dd42e08d7d686); scratch `tmp/gm13/` (full3.log, scripts/resolve.py).
- Full build 2 (`tmp/gm12/full2.log`, 27532fcf83): EXIT 1, 13 modules: membership OwnedMutex, os LstatAnyS,
  rpc Client__CloseClosed, http ServeLemmas, gryff Lib.NetAddr and N.ConnErr (all from build 1); rpcdriver
  `dial` (the spec change held but `wp_start` consumes the `isPkgInit net` conjunct: re-obtained by
  `solve_pkg_init`), vr `network.Serve` (not reached in build 1), kvraft TopLevelRobustness (intro arity),
  gryff server1-4 Boot (generated, stale after the sync/runtime → internal/gomodel imports).
- Fixed (b32b450571, 47d14c7096): gryff `wp_TCPAddr_String` and vr's over `net.wp_extAnyString` (as
  swiftpaxos's); gryff `opErrPtr_errAny` takes `opErrMsgOk ∗ errnoOk`, new `resErr_errAny_sys`, errnoOk
  threaded through `rdErr_conn(')`, `resErr_errAny(')`, `resErr_errAny_m` and their callers (Connect,
  WaitPeers, ClientConn, Serve, MasterNew, ServeProof, ReadFullLt); LstatAnyS over `os.modelStat` (StatS's
  shape, `wp_pathError_errnoV`); rpc CloseClosed `connAt_errnoOk`; http ServeLemmas (crErrId carries the
  OpError's netOwnErr/addrOrNil, readErr_msgOk takes `edTyped`, Timeout gets `opErrOk`; `wp_Fprintf_noVerb`
  over fmt's Go-model printer, callees threaded to conn.serve and Results); OwnedMutex = lean's
  (Proof/sync/MutexOwned); kvraft/kvraft_udp intros lose field_sem/os_file_sem/os_stat_sem; gryff boots
  regenerated (`etc/dsv/_gryff_boot.py`). packet-rest.md: new section "Internal spec and lemma changes".
- lean moved to 2926d09437 (basic slice landed + dsv-fix6). A trial merge (aborted) gives 155 conflicts:
  ~120 generated PkgTables (regenerate), lakefile/manifest (keep our pin 09bd3826c), etc/gen-link.py,
  32 Dsverify craq/other files resolved mechanically by `tmp/gm13/scripts/resolve.py` (ours = strip_fa(base)
  → take strip_fa(lean)), and 9 by hand: craq TopLevelRobustness (intro without hlog and fsem), raxos
  SharedLoop (lean's), and **Net rpc/http error lemmas (ReadResponse, Client__input, Client__send,
  DialHTTPPath, HttpDefs) where dsv-fix6's errLeaf/errPlain design over the old trusted OpError meets
  egnet's errStr/errnoOk over Go's OpError** (needs a design merge; dsv-fix6's own finding
  net-operr-error is what the Go model fixes), plus k8s clock NewTicker/NewTimer. Not done in session 13.
- Builds 3-7 (`tmp/gm13/full{3..7}.log`) found the modules behind the first failures: etcd/k8s single-process
  and putget intros (the predecessor had removed 1 of 3 FA binders: now all 3), mvcc `absent` intros, http
  `conn.serve` (TCPAddr.String over the model) and `Server.Serve`'s accept error (`opErrOk` from `resErr`
  via `kindErr_netOwnErr`/`opErr_opErrOk`, for `Temporary` and `opError_argOk`/`wp_logf_accept`), rpcdriver
  TopLevelRobustness intro. **Full build 7: EXIT 0, 28899 jobs.** tcb-report --check: matches (378 axioms,
  0 sorry); collections kvraft, kvraft-udp, raft-noax --check: 0/0 each. NetFsUdp.Adequacy + kvraft_udp TLR
  built explicitly (EXIT 0). packet-rest.md: head table, Evidence, internal-spec section updated.
- STATE at end of session 13: lmerge head = egnet head (fast-forwarded, pushed). LEFT: merge lean
  `2926d09437` (see the trial-merge item above: keep pin 09bd3826c; regenerate PkgTables/BootTables, gen-init,
  copy-part, gen-link; the dsv-fix6 Net rpc/http error lemmas need a design merge: lean's errLeaf/errPlain
  vs egnet's errStr/errnoOk over Go's OpError.Error), then rebuild and re-run tcb.

## Session 14 (2026-11-26, successor) — merge of lean `2926d09437` (basic slice + dsv-fix6)
- Worktree `eg-lmerge`, NEW branch `go-models-rest-egnet-lmerge2/2026-11-26` (off 75c8e1c837), VM key
  c61dd42e08d7d686; scratch `tmp/gm14/` (merge.log, conflicts.txt, scripts/{hunks.py, regen.sh, *.py the
  per-file resolutions}, b*.log, full*.log).
- #8: no reply after 21:00Z; coordinator relayed coordinator-E 7173879212: keep the go-models route,
  re-prove dsv-fix6's lemmas with statements unchanged where possible, any craq-side change only ADDS
  facts Go's real Error provides, no top-level statement touched, the diff posted on #8 for
  etcd-grove-03 before landing; record that this closes `net-operr-error`.
- Merge `c86c1b291d`: 187 conflicts. 143 generated PkgTable/BootTable: took lean's, regenerated
  (`tmp/gm14/scripts/regen.sh WT write`: gen-init, copy-part, gen-raft-tla, gen-specs-pkginit, kitgen,
  rpcdriver-boottable, k8s-deep, pbschema; then `tmp/gomodels/s10/genlink-all.sh WT --write`: 0 differ) —
  result identical to ours (same pin). lakefile/manifest ours (09bd3826c). etc/gen-link.py ours (no FA
  entries; lean's only change there was dropping MutexLitSemantics, which ours already had). 32 craq/dsv
  files by `tmp/gm13/scripts/resolve.py`; craqnet TLR intro without hlog/fsem; raxos SharedLoop and k8s
  clock NewTicker/NewTimer = lean's. Errs.lean (auto-merged) lost its `field_sem` binder.
- Design merge (dsv-fix6 errLeaf/errPlain over Go's translated `OpError.Error`), statements changed only
  by ADDED premises/facts (list in packet-rest.md, "dsv-fix6 lemmas over the Go-model net"):
  `crErr` = lb ∗ `net.errStr` ∗ `⌜errLeaf⌝`; `ReadResponse.spec_errs` + errStr premise/post;
  `errPlain_opErr`/`errPlain_resErr` + `syscall.errnoOk` (+ errStr/addrOrNil for opErr), their pure
  `errLeaf` address premises dropped (implied by `addrOrNil`); `errPlain_opErrPtr` curried
  `pe ↦□ v ⊢ errnoOk -∗ opErrMsgOk v -∗ errPlain`; `inErr_read` + errnoOk (lean's netAddr la/ra not
  needed); `readErr_some'` gives errLeaf too; `DialHTTP(Path).spec_plain` + `isPkgInit net`.
- Results: targeted builds b1-b3 (`tmp/gm14/b{1,2,3}.log`; fixed: `wp_errors_New'`'s post now
  `x.s ↦□ ∗ wp`, DialHTTPPath.wp_proof's derivation re-obtains `isPkgInit net` by solve_pkg_init after
  wp_start_folded, ReadResponse.wp's pattern) then **full default build EXIT 0, 28901 jobs**
  (`tmp/gm14/full1.log`, code 42f4df0a18). `tcb-report --check`: matches lean's baseline (381 axioms, 0 sorry);
  **all 64 collections --check match** (`tmp/gm14/tcb.log`; kvraft, kvraft-udp, raft-noax 0/0; dsv-craq
  6 = lean's). NetFsUdp.Adequacy + kvraft_udp TLR up to date (`lake build --no-build`, 4559 jobs).
  Statements vs lean: craq's spec, Iface, LogHyp, LogAx, ErrFmt differ from lean only by the
  FieldAssumptions binders (removal). net-operr-error: closed (packet-rest.md, last section; argued).
- STATE: `go-models-rest-egnet/2026-11-24` fast-forwarded to this branch's head (pushed). LEFT: the #8
  message (diff for etcd-grove-03, in the session report); merge newer lean when it moves.

## Session 15 (2026-11-26, successor) — merge of lean `5c036beb77` (grpc-driver)
- Worktree `eg-lmerge`, NEW branch `go-models-rest-egnet-lmerge3/2026-11-26` (off 661702e0cb), VM key
  c61dd42e08d7d686; scratch `tmp/gm15/` (merge.log, conflicts.txt, changed.txt, strip.log, regen1.log,
  goose-check.log, full*.log).
- lean's Perennial pin is still d5eb93cb5 (an ancestor of ours): kept ours, 09bd3826c.
- Merge: ONE conflict, auth/Results.lean `authkv_Main` (lean renamed the docstring's `grpc.start` to
  `grpcServeTok`; ours had dropped the FA binders): lean's docstring, our binders. strip_fa.py over the 265
  .lean files the merge added/changed: 4 files (grpcdriver Link, ListenSet, Server, TLR spec); the TLR
  proof's intro loses `field_sem`. Regenerated (regen.sh: gen-init rewrote grpcdriver cmd/{client,server}
  PkgTables for our Go-model closure; others unchanged) and genlink-all (0 differ).
- grpc-driver needed no design merge: it adds no trusted net assumption (its trusted part is grpc's model
  and wrapperspb's `String`); it calls Net's `net.Listen.spec` as a hypothesis. Port: `drv_listen`
  (ListenSet.lean) takes `isPkgInit pkg_id.net` in its precondition (ours `Listen.specAddrOk` needs it;
  internal lemma, listed in packet-rest.md); `Server.wp_proof` obtains it by `iPkgInit`.
- goose.py --check (eggoose.sh, nested Perennial 09bd3826c): 73 projects up to date (`tmp/gm15/goose-check.log`).
- **Full default build EXIT 0, 29034 jobs, first try** (`tmp/gm15/full1.log`, code b8bb95f0ba).
  `tcb-report --check`: matches lean's baseline (384 axioms, 0 sorry); all 65 collections `--check --reuse`
  exit 0 (`tmp/gm15/tcb.log`, script `tmp/gm15/scripts/tcb.sh` via `vmlake sh`). NetFsUdp.Adequacy + kvraft_udp
  TLR (`KvRaft.Proof....raft.kvraft.cmd.kvraft_udp.TopLevelRobustness`) up to date (`lake build --no-build`).
  packet-rest.md: head row, Evidence, new last section "grpc-driver over the Go-model net".
- STATE: `go-models-rest-egnet/2026-11-24` fast-forwarded to this branch's head (pushed). LEFT: #8 message;
  merge newer lean when it moves.
