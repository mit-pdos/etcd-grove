/-
The package-initialization instance of this repository's `internal/syscall/unix` (project bboltfs's
translation, `Code/internal/syscall/unix.lean`, 2026-11-07; Perennial's imports Perennial's
`syscall`). Its fact is `True`: nothing reads its one variable (`faccessat`). Its `wp_initialize'`
is `Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Fs.Impl
public import Perennial.GeneratedProof.sync
public import Perennial.Golang.Theory
public import Code.syscall
public import Code.internal.syscall.unix
public import Perennial.Proof.ProofPrelude
public import Proof.syscall.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace internal.syscall.unix

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.syscall.unix :=
  define_is_pkg_init iprop(True)

end internal.syscall.unix

end init

end Perennial
