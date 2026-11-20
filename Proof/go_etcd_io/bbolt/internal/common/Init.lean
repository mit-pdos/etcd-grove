/-
Package initialization of `go_etcd_io.bbolt.internal.common`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`bboltCommonInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `DefaultPageSize` holds
4096, for good. Its initializer allocates `DefaultPageSize`, initializes its imports and
runs its translated initializer, `DefaultPageSize = os.Getpagesize()` (`types.go`), whose callee is
names-only in Perennial: the trust-boundary axiom `os.Getpagesize.wp_proof` (4096 on linux/amd64).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unsafe.Link
public import Proof.go_etcd_io.bbolt.errors.Init
public import Proof.hash.fnv.Init
public import Proof.os.Init
public import Proof.runtime.Init

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
