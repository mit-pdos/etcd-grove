/-
Package initialization of `go_etcd_io.bbolt`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`bboltRootInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `runtime.GOOS` is
`"linux"` and `runtime.GOARCH` `"amd64"` (the trust-boundary axioms `runtime.GOOS_linux` and
`runtime.GOARCH_amd64` of `runtime`'s `Init.lean`; bbolt compares `GOOS` with `"windows"` in
`DB.grow`, `DB.mmap` and `DB.allocate`, and its loggers format both). Its initializer allocates its variables, initializes its imports and
runs their translated initializers: `trySolo` (an `errors.New` call, `db.go`; Perennial's
`errors.wp_New_errorString`), the deprecated aliases of
`errors`' variables (loads of them), `discardLogger` (`&nopLogger{}`, the fork's no-op logger,
which the fact records: a `*nopLogger`), and `DefaultOptions` (`&Options{...}`, an allocation;
translated since 2026-11-17, `Code/go_etcd_io/bbolt.toml`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unsafe.Link
public import Proof.encoding.hex.Init
public import Proof.go_etcd_io.bbolt.errors.Init
public import Proof.go_etcd_io.bbolt.internal.common.Init
public import Proof.go_etcd_io.bbolt.internal.freelist.Init
public import Proof.golang_org.x.sys.unix.Init
public import Proof.os.Init
public import Proof.runtime.Init
public import Proof.syscall.Init
public import Perennial.Proof.errors.NewVar

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
