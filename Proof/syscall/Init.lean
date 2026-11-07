/-
Package initialization of `syscall`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True` (`Proof/syscall/PkgInit.lean`). Its initializer initializes `sync`
and runs its variables' translated initializers (`envs = runtime_envs()`, whose trusted model is an
arbitrary `[]string`; `copyenv = sync.OnceFunc(...)`, constants, a map, `sync.Pool` and `mmapper`
literals), then its `init` function, whose trusted model does nothing (`TrustedCode/syscall.lean`:
the RLIMIT_NOFILE raise, unobservable to what Perennial models).
-/
module

public import Proof.syscall.PkgInit
public import Perennial.Proof.sync.Link
public import Proof.syscall.Models
public import Perennial.Proof.sync.Link
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
namespace syscall
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `syscall`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end syscall
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.syscall.Assumptions]

namespace syscall

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.syscall get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.syscall }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) signals _ as Hsignals
  wp_apply wp_GlobalAlloc (V := _) errors _ as Herrors
  wp_apply wp_GlobalAlloc (V := _) errENOENT _ as HerrENOENT
  wp_apply wp_GlobalAlloc (V := _) errEINVAL _ as HerrEINVAL
  wp_apply wp_GlobalAlloc (V := _) errEAGAIN _ as HerrEAGAIN
  wp_apply wp_GlobalAlloc (V := _) Stderr _ as HStderr
  wp_apply wp_GlobalAlloc (V := _) Stdout _ as HStdout
  wp_apply wp_GlobalAlloc (V := _) Stdin _ as HStdin
  wp_apply wp_GlobalAlloc (V := _) mapper _ as Hmapper
  wp_apply wp_GlobalAlloc (V := _) pageBufPool _ as HpageBufPool
  wp_apply wp_GlobalAlloc (V := _) fcntl64Syscall _ as Hfcntl64Syscall
  wp_apply wp_GlobalAlloc (V := _) forceClone3 _ as HforceClone3
  wp_apply wp_GlobalAlloc (V := _) slash _ as Hslash
  wp_apply wp_GlobalAlloc (V := _) none' _ as Hnone'
  wp_apply wp_GlobalAlloc (V := _) copyenv _ as Hcopyenv
  wp_apply wp_GlobalAlloc (V := _) envs _ as Henvs
  wp_apply wp_GlobalAlloc (V := _) env _ as Henv
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of envs))
  -- translated initializer of copyenv))
  -- translated initializer of none'))
  -- translated initializer of slash))
  -- translated initializer of forceClone3))
  -- translated initializer of fcntl64Syscall))
  -- translated initializer of pageBufPool))
  -- translated initializer of Stdin))
  -- translated initializer of Stdout))
  -- translated initializer of Stderr))
  -- translated initializer of errEAGAIN))
  -- translated initializer of errEINVAL))
  -- translated initializer of errENOENT))
  -- translated initializer of mapper))
  -- translated initializer of errors))
  -- translated initializer of signals))
  wp_func_call
  unfold runtime_envs.impl
  wp_apply syscall.wp_arbitraryStrings as %envsl ⟨%xs, Henvsl, Henvscap⟩
  set_option maxRecDepth 20000 in
  wp_apply _root_.Perennial.sync.wp_OnceFunc as %cpe -
  try unfold EAGAIN EINVAL ENOENT
  repeat (first
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_map_make1 (K := Loc) (V := GoSlice) as %mref Hm
  try wp_auto
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  -- translated initializer of env))
  -- translated initializer of envs))
  -- translated initializer of env))
  -- translated initializer of env))
  -- translated initializer of envs))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.syscall get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.syscall }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end syscall

end init

end Perennial
