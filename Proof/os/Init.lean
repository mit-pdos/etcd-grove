/-
Package initialization of `os`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`Proof/os/PkgInit.lean`): `Stderr` holds a fixed `*File`, which raft's
initializer loads (`defaultLogger`). `os` is this repository's translation (project bboltfs's,
names only but for the types and the functions the Linux file extension models): its initializer
initializes its imports, runs its variables' untranslated initializers, which the trust-boundary
axiom `opaqueInitsOk` says run without panicking (`Stderr_init` the one the fact reads: `Stderr =
NewFile(uintptr(syscall.Stderr), "/dev/stderr")` gives the variable some `*File`), and its
untranslated `init` function, which `initFuncsOk` says returns. (Until 2026-11-03, over Perennial's
`os`, in raft's `Init.lean`.)
-/
module

public import Proof.os.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Proof.io.fs.Init
public import Proof.syscall.Init
public import Proof.runtime.PkgInitExt

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
namespace os
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `os`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([dirBufPool.init,
        ErrInvalid.init,
        ErrPermission.init,
        ErrExist.init,
        ErrNotExist.init,
        ErrClosed.init,
        ErrNoDeadline.init,
        ErrDeadlineExceeded.init,
        ErrProcessDone.init,
        errProcessReleased.init,
        ErrNoHandle.init,
        Interrupt.init,
        Kill.init,
        Stdin.init,
        Stdout.init,
        errWriteAtInAppendMode.init,
        errPathEscapes.init,
        checkWrapErr.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        checkPidfdOnce.init,
        errPatternHasSeparator.init,
        pollCopyFileRange.init,
        pollSplice.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `os`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `Stderr = NewFile(uintptr(syscall.Stderr), "/dev/stderr")` (`os/file.go`): the variable
holds some `*File` (what `os`'s fact reads; raft's `defaultLogger` loads it). The variable's
cell is given here: its initializer is untranslated, so no `GlobalAlloc` of it is translated. -/
axiom Stderr_init :
    {{ (True : IProp GF) }} (App (Val Stderr.init) (Val #()))
    {{ RET #(); ∃ f : Loc, globalAddr Stderr ↦ f }}

end os
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.os.Assumptions]

namespace os

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.os }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.syscall.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.io.fs.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk dirBufPool.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalid.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrPermission.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNotExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClosed.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNoDeadline.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrDeadlineExceeded.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrProcessDone.init (by mem_tac))
  wp_apply (opaqueInitsOk errProcessReleased.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNoHandle.init (by mem_tac))
  wp_apply (opaqueInitsOk Interrupt.init (by mem_tac))
  wp_apply (opaqueInitsOk Kill.init (by mem_tac))
  wp_apply (opaqueInitsOk Stdin.init (by mem_tac))
  wp_apply (opaqueInitsOk Stdout.init (by mem_tac))
  wp_apply Stderr_init as ⟨%stderr, HStderr⟩
  wp_apply (opaqueInitsOk errWriteAtInAppendMode.init (by mem_tac))
  wp_apply (opaqueInitsOk errPathEscapes.init (by mem_tac))
  wp_apply (opaqueInitsOk checkWrapErr.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk checkPidfdOnce.init (by mem_tac))
  wp_apply (opaqueInitsOk errPatternHasSeparator.init (by mem_tac))
  wp_apply (opaqueInitsOk pollCopyFileRange.init (by mem_tac))
  wp_apply (opaqueInitsOk pollSplice.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist HStderr
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.os }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end os

end init

end Perennial
