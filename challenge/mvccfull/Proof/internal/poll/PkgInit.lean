/-
The package-initialization instance of this repository's `internal/poll` (project bboltfs's
translation, `Code/internal/poll.lean`, 2026-11-07; Perennial's imports Perennial's `syscall`). Its
fact: the two error variables `os`'s initializer copies (`ErrNoDeadline`, `ErrDeadlineExceeded`)
hold some error, for good (Go never writes them after initialization). Its `wp_initialize'` is
`Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.errors
public import GooseLang.Ext.Fs.Impl
public import Perennial.GeneratedProof.sync
public import Perennial.Golang.Theory
public import Code.syscall
public import Code.internal.syscall.unix
public import Code.internal.poll
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors
public import Perennial.Proof.sync.Base
public import Proof.syscall.PkgInit
public import Proof.internal.syscall.unix.PkgInit

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

namespace internal.poll

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.poll :=
  define_is_pkg_init iprop((∃ e : GoInterface, typedPointsto (globalAddr ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr ErrDeadlineExceeded) e DFrac.discard))

end internal.poll

end init

end Perennial
