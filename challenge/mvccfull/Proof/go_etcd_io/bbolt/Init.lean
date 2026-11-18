/-
Package initialization of `go_etcd_io.bbolt`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`bboltRootInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `runtime.GOOS` is
`"linux"` and `runtime.GOARCH` `"amd64"` (the trust-boundary axioms `runtime.GOOS_linux` and
`runtime.GOARCH_amd64` of `runtime`'s `Init.lean`; bbolt compares `GOOS` with `"windows"` in
`DB.grow`, `DB.mmap` and `DB.allocate`, and its loggers format both). Its initializer allocates its variables, initializes its imports and
runs their translated initializers: `trySolo` (an `errors.New` call, `db.go`; Perennial's
`errors.wp_New_errorString`), the deprecated aliases of
`errors`' variables (loads of them), and `discardLogger` (`&nopLogger{}`, the fork's no-op logger,
which the fact records: a `*nopLogger`).
And `DefaultOptions`' untranslated initializer (`Options` is an axiomatized type,
`Code/go_etcd_io/bbolt.toml`), which the trust-boundary axiom `opaqueInitsOk` says runs.
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
public import Proof.go_etcd_io.bbolt.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVar
public import Spec.fmt.ErrorOk
public import Perennial.Proof.errors
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unsafe.Link
public import Proof.hash.PkgInit
public import Proof.os.PkgInit
public import Perennial.Proof.sync.Link
public import Proof.internal.poll.PkgInit
public import Proof.internal.syscall.unix.PkgInit
public import Proof.syscall.PkgInit
public import Code.syscall
public import Perennial.Proof.fmt.SprintfModel
public import Perennial.Proof.internal.oserror.Link
public import Code.os
public import Proof.runtime.Init
public import Proof.os.Getpagesize
public import Perennial.Proof.math.Link
public import Proof.reflect.Init
public import Proof.golang_org.x.sys.unix.Init
public import Proof.runtime.Init
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

section opaqueInits
namespace go_etcd_io.bbolt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.bbolt`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([DefaultOptions.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end go_etcd_io.bbolt
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.bbolt.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.bbolt

end go_etcd_io.bbolt

end init

end Perennial
