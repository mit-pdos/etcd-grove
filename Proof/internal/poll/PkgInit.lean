/-
The package-initialization instance of this repository's `internal/poll` (project bboltfs's
translation, `Code/internal/poll.lean`, 2026-11-07; Perennial's imports Perennial's `syscall`). Its
fact: the two error variables `os`'s initializer copies (`ErrNoDeadline`, `ErrDeadlineExceeded`)
and `ErrFileClosing`, which `(*os.File).wrapErr` compares with (2026-11-22), hold some error, for good
(Go never writes them after initialization). Its `wp_initialize'` is
`Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import GeneratedProof.internal.poll
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
    (∃ e : GoInterface, typedPointsto (globalAddr ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr ErrFileClosing) e DFrac.discard))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.poll :=
  build_get_is_pkg_init_wf

/-- `poll.ErrFileClosing` holds some error, for good (`(*os.File).wrapErr` compares with it). -/
theorem errFileClosing_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
    ∃ e : GoInterface, typedPointsto (globalAddr ErrFileClosing) e DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr ErrFileClosing) e DFrac.discard)) ⊢ _
  iintro ⟨-, -, He⟩
  iexact He

end internal.poll

end init

end Perennial
