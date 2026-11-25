# Axiom review: `os/signal.Notify`'s environment claims (`wp_proofQuietSigs`, `wp_proofUsr1Sigs`)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`) at `a28755b089`; Perennial `fce59af75`; Go at the
pinned toolchain go1.27.3 (`src/os/signal/signal.go`, `signal_unix.go`, `runtime/sigqueue.go`).

## The axioms

`Dsverify/Proof/os/signal/Notify.lean`:

    axiom os.signal.Notify.wp_proofQuietSigs : os.signal.NotifyQuiet.spec quietSigs   -- [SIGINT(2), SIGTERM(15)]
    axiom os.signal.Notify.wp_proofUsr1Sigs  : os.signal.NotifyQuiet.spec usr1Sigs    -- [Signal(0xa) = SIGUSR1]

over (`Dsverify/Proof/os/signal/Spec.lean`)

    NotifyQuiet.spec sigs := sigs ≠ [] → ∀ c sig dq, c ≠ chan.nil →
      {{ isPkgInit pkg_id.os.signal ∗ sig ↦*{dq} sigs }} os.signal.Notify c sig {{ RET #(); sig ↦*{dq} sigs }}

`os/signal` is translated names only (`Dsverify/Code/os/signal.lean`); `isPkgInit pkg_id.os.signal`
is `True` (reviewed in `../dsv-inits/os-signal.md`).

Claims, in plain words:
1. `Notify` on a non-nil channel, with exactly that list, returns without panicking and gives back
   the slice (it does not keep it).
2. It touches nothing the caller owns: the frame rule keeps the caller's ghost state of `c`, so no
   model step ever sends on `c`. The callers turn this into "`c` never receives": they make `c` a bag
   of `False` (`start_bag`) before the call (`SigListen.lean`, `HookUser1.lean`), so a receive on it
   is unreachable. This is the environment claim: in Go, `c` receives only when one of the listed
   signals is delivered to the process, and nobody sends one.
3. Each axiom is for its one list (the slice must hold exactly `quietSigs` / `usr1Sigs`); the empty
   list is excluded.

Uses: `wp_proofQuietSigs` instantiates `os.signal.NoSignals quietSigs` in rabia's closed result
(`Dsverify/Proof/rabia/examples/rabianet/TopLevelRobustness.lean:191`), consumed by
`internal/system.SigListen` (`signal.Notify(sigIn, syscall.SIGINT, syscall.SIGTERM)`, constants
inlined by Goose as `#(W64 2)`, `#(W64 15)`). `wp_proofUsr1Sigs` is not used yet at this commit:
swiftpaxos's statement still has the premise `∀ G L, os.signal.NoSignals usr1Sigs`
(`Dsverify/Spec/.../swiftnet/TopLevelRobustness.lean:102`); `hook.HookUser1` passes
`syscall.Signal(0xa)`.

## Verdict: **survives with conditions**

No Go program within the model's reach panics while a no-panic triple follows from these axioms.
The claim is an environment claim, correctly scoped to the listed signals, under these conditions
(stated or to be stated beside the axioms):

- **C1 (the claim itself)**: no process (operator, launcher, supervisor) sends SIGINT, SIGTERM or
  SIGUSR1 to any process of the deployment, including through the terminal (Ctrl-C reaches the whole
  foreground process group: the robust harness starts machines without `Setpgid`, so a Ctrl-C on
  `go test` reaches them), `timeout(1)`/`systemd`/container stop (SIGTERM by default), and a
  launcher's `Pdeathsig` (the kernel then sends the chosen signal itself; the harness uses SIGKILL,
  `examples/lib/robust/proc.go:34`). The rabia statement's header says this; the swiftpaxos one says
  it as its premise.
- **C2 (platform)**: Linux on an architecture with the generic signal numbers (amd64, arm64, 386,
  arm, riscv64, ppc64, s390x: SIGUSR1 = 10). On linux/mips `Signal(0xa)` is SIGBUS and SIGUSR1 is
  16, so `usr1Sigs` would name another signal (the swiftpaxos fork writes the literal `0xa`;
  `hook/sigusr1_test.go` checks it on the build host only).
- **C3 (bookkeeping)**: at `a28755b089` neither axiom is in `etc/tcb-baseline.txt` nor in
  `etc/tcb-collections/dsv-rabia.txt`, although the rabia statement's header says every axiom it rests
  on is listed there; `--check --update` must add `wp_proofQuietSigs` (and `wp_proofUsr1Sigs` to
  `dsv-swiftpaxos.txt` once swiftpaxos's premise is replaced).

## Attacks tried

1. **A missing premise (Notify panics).** Go's `Notify` (`signal.go`) panics only on a nil channel
   ("os/signal: Notify using nil channel", confirmed by the scratch test below), excluded by
   `c ≠ chan.nil`. Otherwise: map insert under the package lock, `signum` (out-of-range values give
   -1 and are skipped, but 2/15/10 are in range), `enableSignal` → `runtime.signal_enable`/`sigenable`
   (no panic path), and `watchSignalLoopOnce.Do(go loop())`. No other runtime error.
   A wrong-direction channel cannot be passed (Go's type `chan<- os.Signal`; the translation converts
   `sigIn` to send-only).
2. **Signals the runtime or kernel sends by itself.** `Notify(c)` with no list does receive without
   any sender: the scratch test, spinning 8 goroutines for 2 s, got 100 `urgent I/O condition`
   (SIGURG, async preemption) — the reason `sigs ≠ []` is required, and it is. The go1.27.3 runtime
   never raises SIGINT, SIGTERM or SIGUSR1 (`grep _SIGINT|_SIGTERM|_SIGUSR1 runtime/*.go`: only the
   `sigtable` entries and a test hook); it raises only the signal it is dying from, SIGURG, SIGPROF.
   The kernel sends SIGPIPE, SIGCHLD, SIGSEGV/SIGBUS, SIGXCPU, SIGHUP (terminal hangup), SIGKILL
   (OOM), SIGURG (socket OOB data), none in the lists; SIGINT comes from the tty line discipline
   (C1); SIGTERM/SIGUSR1 never unless asked (`Pdeathsig`, C1). Scratch test: `q` (SIGINT, SIGTERM)
   and `u` (Signal(0xa)) stayed empty through the preemption storm and a broken-pipe write.
3. **A process sending itself one.** Real (`syscall.Kill(os.Getpid(), SIGUSR1)` is delivered to
   `u`, scratch test), but not provable: no spec or model of this repository or Perennial sends a
   signal (no `syscall.Kill`, `os.Process.Signal/Kill`, `exec` in any `Spec`/`Proof`/extension
   `Impl`), and the verified Go of rabia and swiftpaxos sends none (`grep`: only `os.Getpid()` for a
   file name in `swift/execlog.go`). A counterexample would need another axiom, which would itself
   have to model the signal, so it is not one against these.
4. **The claim leaking to other lists or channels.** Each axiom fixes its list by value
   (`sig ↦*{dq} quietSigs`); another list (`[]`, SIGHUP, SIGQUIT, …) gets nothing. Any non-nil `c`
   with the same list is fine: if no listed signal is sent at all, no channel registered for them
   receives. Repeated `Notify` on the same `c`, or `Notify` of another channel for other signals,
   does not make Go deliver a listed signal to `c` (`process` sends to a channel only for a signal
   `n` its handler wants, and only when `n` arrives; the `stopping` list likewise).
5. **Closed or full channel.** Go's delivery (`process`) does `select { case c <- sig: default: }`,
   which would panic on a closed `c`; only with a delivery, so excluded by C1. Neither caller closes
   its signal channel.
6. **Too much ownership / effects beyond the frame.** Go's `Notify` reads the slice only during the
   call (fraction `dq` returned), writes only `os/signal` package state that no Lean proof owns
   (names-only translation). It starts goroutines (`loop`, the runtime's `ensureSigM`), which the
   model does not: they block forever in `signal_recv` without any signal and cannot panic; the two
   extra goroutines are irrelevant to rabia's statement (any number of threads) and negligible against
   swiftpaxos's `2^30` bound.
7. **Cross-world entailment.** Not applicable: a triple with no pure conclusion about an opaque
   function of a pointer.
8. **Inconsistency.** As every names-only axiom, it is stated for every Go context in which
   `os/signal.Notify` resolves to whatever body; false in a context where it resolves to a panicking
   one, but no such concrete context exists (the interim trust shared with the initializer axioms,
   `../dsv-inits/os-signal.md` item 8).

Why the claim matters (not a counterexample): with a SIGINT/SIGTERM, rabia's `SigListen` closes the
server's `Done` (`roles/server/server.go:112,137`), stopping the server; the proof's `False` branch
covers that path only because of C1.

Scratch check (`/shared/tmp/osnotify-review`, removed): go1.27.3, `TestQuiet` (the quiet channels
empty after 2 s of forced preemption and a broken-pipe write; `Notify(all)` with no list got 100
SIGURG; self-sent SIGUSR1 delivered to `u`) and `TestNil` (nil channel panics), both as described.

Not tried: a Lean counterexample (no gap to build one on); other platforms than linux/amd64.

## Proposed restatement

None needed. Suggested (not applied): name C2 in the axioms' docstring (Linux, generic signal
numbers) and C1's launcher cases (`Pdeathsig`, process-group Ctrl-C); fix C3.

No Go bug found.
