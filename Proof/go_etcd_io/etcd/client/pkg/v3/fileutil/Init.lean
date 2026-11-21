/-
Package initialization of `go_etcd_io.etcd.client.pkg.v3.fileutil`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`fileutilInit`, `PkgInit.lean`): the lock functions `linuxLockFile`/`linuxTryLockFile`
(both OFD's or both `flock`'s), the write-lock description `wrlck` and `ErrLocked` (an error whose
`Error()` returns), read-only for good. Its initializer stores `ErrLocked` (a translated `errors.New`),
`wrlck` (a struct literal) and the `flock` functions, initializes its imports and runs its translated
`init` function (lock_linux.go), which probes OFD locks with `F_OFD_GETLK` on fd 0 and switches both
functions to OFD's on success: the probe's errno is any (`syscall.FcntlFlock.wp_getlk`), so either
outcome.
-/
module

public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import Proof.bufio.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_uber_org.zap.Init
public import Proof.golang_org.x.sys.unix.Init
public import Proof.io.fs.Init
public import Proof.os.Init
public import Proof.path.filepath.Init
public import Proof.syscall.Init
public import Perennial.Proof.errors.NewVar
public import Proof.syscall.FileOps
public import Proof.errors.ErrorStringOk

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end Perennial
