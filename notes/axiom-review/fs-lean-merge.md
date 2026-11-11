# Review of the trusted changes of `fs-lean` (merge `c7599df2e9`, page cuts `71480b7148`), 2026-11-11

Reviewed at `fs-lean` `76837da5cc`, read through `git show` (no build). Scripts: `fs-lean-merge/`
(`extract.sh OUT` writes both parents', the base's and `fs-lean`'s trusted files for a `diff3`;
`netpoll/run.sh WORKDIR` is the `RLIMIT_NOFILE` experiment). Go sources: the pinned go1.27.3.

Verdict: **no counterexample.** The page-cut rule survives, the merge of the trusted models is
the union of both sides, and the new spec conjuncts are proved. One latent problem was carried
by the merge (finding 1). The rest are justification text and documentation.

## Summary

| # | severity | finding | fix |
|---|---|---|---|
| 1 | **medium** (latent; on fs-bytes before the merge) | `axiom os.Rename.wp_proof` (`Proof/os/Rename.lean:32`, `Spec/os/Rename.lean`) now states a spec of a **modelled** function. On lean, `os.Rename` was names-only, and the axiom's docstring still says so. On fs-lean it is `TrustedCode/os.lean`'s `Rename.impl`, the Fs extension's `CallBegin`/`LstatDir`/`Rename`. The axiom's pre and post are backend vocabulary (`fileHolds`, an `axiom`; `pathOwn`, an `opaque`), with no Fs resource and for any `GooseExts`. So the same code has two trusted specs that do not connect: walfs proves its renames from the model (`DirSwap.lean:855`, `Boot.lean:889`), and the server (`etcdserver/Link.lean:1020`) assumes this one. | Today no theorem has both `pathOwn` (a server boot premise, `InvBoot.lean:454`) and Fs ownership of the same tree, so nothing is derivable now. Any future theorem with both could rename under the Fs invariant: the Fs ghost state says `dst` holds the old file, while the machine holds the new one. Fix: update the docstring (no longer names-only), and record in STATUS and the bbolt port plan that when the server moves onto Fs the axiom must be replaced by a proof from `Rename.impl`, with `fileHolds`/`pathOwn` defined over the Fs tree. Until then, no theorem may take `pathOwn` together with `osInv`. |
| 2 | low (page cuts, the justification) | "An unreadable source buffer (a Go slice is readable)" is broader than what the kernel argument needs. The in-page cuts need a source page that **cannot be faulted in**, or a failure after a short atomic copy into an uptodate folio. The model's `WriteAt` accepts a slice of a read-only mapping, whose cells are bytes, and the kernel reads that page from the file. If that fault fails (a memory-cgroup OOM that returns `VM_FAULT_OOM` to a kernel-mode access gives `EFAULT` after progress), the cut is mid-page. Also from the source, not measured: a short copy (a source page under migration, measured as real in `fs-v2-r6`) followed by an `ENOMEM` in the next `write_begin` (a jbd2 handle on the non-delalloc path near full, or a folio re-allocated after eviction) stops mid-page with errno 0. C excludes journal aborts (no error or shutdown event) but says nothing about allocation failure. | None needed for today's clients: every `WriteAt` source in `examples/osfs` and bbolt is a heap buffer, and the kernel's small allocations do not fail for a task that is not being killed. Either make the docstring precise ("every page of the source can be faulted in: heap memory; a mapping's page needs a read that cannot fail") and add "no allocation failure in the write path" to the environment beside "no failed writeback", or leave it as a stated residual. |
| 3 | low (doc) | `Impl.lean`'s header says "20 of 20 errors with a page cut landed". The measurement (`bbolt-port-plan-review/README.md`, Part 2) is different: 20/20 errno returns of `pwrite(2)` landed **nothing**, 19/19 short counts ended on a page boundary, and at the Go level 19 `(0, err)` results had a page-cut prefix landed. Also, `Code/go_etcd_io/bbolt.toml:4` still names `osFsExt`. | Reword the sentence. Fix the comment. |
| 4 | info (netpollinit, the new disposition) | Measured (`fs-lean-merge/netpoll/`, go1.27.3, hard `ulimit -n` of 4 and 5): `fatal error: runtime: netpollinit failed` / `eventfd failed` comes **after** `open(2)` created the file (the file exists in both runs). At 6 and above, `OpenFile` returns normally. So a Go run that dies there is a prefix of a model run: `Open`'s step, then the process ends. The restart assumption (`Impl.lean:30-36`) makes the restart a machine crash, and a crash with `O_TRUNC` in flight is covered by the crash rule's "towards the target of a change in flight". The disposition is right for crash results. It is also too pessimistic for Hoare triples. A triple is partial correctness, and a process that stops after a model-matching prefix contradicts no triple, just as `os.Exit` does not (the axiom skill's "What counts"). | Optional: reword `TrustedCode/syscall.lean`'s `init.0` note ("a death after a prefix of the model's run: no triple's claim, and the restart is a crash"). Or add hard `RLIMIT_NOFILE ≥ 6` (systemd's default is 524288) to C's Process row, which removes the gap text. |
| 5 | info (no finding) | The page-cut rule (`Impl.lean:639`) is sound on C for heap sources (finding 2 aside), and it cannot make a client's proof vacuous. It only removes outcomes, and `k = data.length, e = 0` always remains (the witness in `Write.lean:1076`). No proved client uses it yet: `wp_osPWriteFinishK` discards the conjunct, and only `Tests.lean`'s `pwrite_page_cut` and `pageCut_one_page` use it. It is trust added ahead of the bbolt port. | None. |
| 6 | info (no finding) | `os.File.WriteAt`'s model (`TrustedCode/os.lean:308-332`) still reaches every Go outcome (`os/file.go` `WriteAt`, `internal/poll/fd_unix.go` `Pwrite`, go1.27.3). Those outcomes are: `(len, nil)` after any sequence of short counts, page cuts included; `(0, PathError{"write"})`, since `n += m` only runs without an error and `Pwrite` returns `nn < len` only with an error; the `EINTR` retry from the same `nn` (Go's `n = -1`); and the negative offset. Chunks start at `off + nn`, and the rule is on the file offset, as folios are. `io.ErrUnexpectedEOF` stays unreachable, as before. | None. |
| 7 | info (no finding) | The merge of `TrustedCode/os.lean` and `TrustedCode/syscall.lean` equals `diff3` of the two parents over their base (`1fbbd2504b`). The one conflict in each file was a pair of additions, and both were kept, with nothing lost or doubled. In `os.lean`: fs-bytes's tree models (`LinkError`, `Rename`, `Remove`, `Mkdir`, `Readdirnames`) and lean's `runtime_args` and standard streams. In `syscall.lean`: the import, with lean's `fmt` import kept. Lean's only other change was the header line. The models agree with go1.27.3: `rlimit.go`'s `init`, `Errno.Error`, `os.Stdin`/`Stdout`/`Stderr` (`file.go:72-74`). `Code/os.toml` and `Code/syscall.toml` are the union of both lists, with `translate_types` from lean. The `etc/goose.py` change is the `walfs` project entry and comments. The `etc/gen-init.py` change is a docstring. Neither changes what is trusted. | None. |
| 8 | info (no finding) | The specs' new conjuncts are true. `os.File.Sync`/`Truncate`/`Stat` gain `fmtErrorOkOrNil err`, and `Stat` also gains `IsPointerError`. They are proved: there is no `sorry` or `axiom` in `Proof/os/File__{Sync,Truncate,Stat}.lean`. The models return `nil` or a fresh `*PathError` (`wrapErrno`), whose `Error` has no `Format` and calls the trusted `Errno.Error`, which returns some string. | None. |

## Attacks tried on the page-cut rule

These are all from the v7.0 source paths that the bbolt-port-plan review cites. None was a new
measurement, except finding 4.

- **Short count with errno 0, mid-page.** This needs a stop inside a folio after a commit. The
  stops are `RLIMIT_FSIZE` (excluded by C, which `check.sh` checks), `EFAULT` (finding 2), a fatal
  signal (the process dies, which is the restart rule), or a `write_begin` failure on the same
  folio after a short copy. That last one is blocked by the delalloc reservation, which already
  covers the folio's blocks. What remains is `ENOMEM` and journal abort (finding 2). A non-fatal
  signal is never checked.
- **`ENOSPC` in a large folio.** `ext4_da_get_block_prep` reserves per block, and a failure fails
  `write_begin` for the whole folio before any copy, so the cut lands at the folio start.
- **A gap write.** With `k = 0`, `w = c.lo = min off size`, so nothing changes. The measurement
  agrees: the size is unchanged.
- **`s_maxbytes`.** The limit is `2^44 - 4096`, which is page-aligned. The model's own `offMax`
  is larger, and it only adds outcomes.
- **Errno after landed bytes** (`ext4_da_do_write_end`'s `PTR_ERR(handle)`). The rule is
  "whatever the errno", so this case only needs the cut to be on a folio end, which holds unless
  finding 2's short copy is also involved.
- **Vacuity.** No conjunct rules out `k = len`.
- **A mapped source in the model.** Cells past EOF or under a change in flight are holes, so the
  `string` conversion in `WriteAt` is stuck, as `SIGBUS`/`EFAULT` is. The remaining case is
  finding 2.

Not tried: a memory-cgroup OOM run (finding 2's `EFAULT` path), and the `ENOMEM` paths.
