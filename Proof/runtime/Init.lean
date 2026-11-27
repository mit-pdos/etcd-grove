/-
Package initialization of `runtime`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (Perennial's `runtime.isInit`, `Perennial/Proof/runtime/Base.lean`): `buildVersion`,
which `Version` returns, holds some string, read-only for good. Its initializer runs the trusted
model of `buildVersion`'s initialization (Perennial's `TrustedCode/runtime.lean`: it allocates the
variable and stores an arbitrary string, the linker's; Perennial's `runtime.wp_buildVersion_init`,
whose cell is made persistent here), initializes its imports, and runs its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return. Its other 94 initialized
variables are skipped (goose `[[skip]]`, Perennial's `Code/runtime.toml`: the runtime's own tables and
state, which no translated code reads), so its initializer does not run them. (Until Perennial
`160fcf12a`, 2026-11-23, its fact was `True` and `buildVersion` untranslated; until 2026-11-27 the
94 were names-only, run as `X.init`s that the trust-boundary axiom `opaqueInitsOk` said return.)

And the trust-boundary assumptions `GOOS_linux` and `GOARCH_amd64`: the program runs on
linux/amd64 (`runtime.GOOS` and `runtime.GOARCH`, constants that goose leaves axiom `val`s, are
`"linux"` and `"amd64"`), as the repository's other platform facts
assume linux/amd64 (`os.Getpagesize` returns 4096, `Spec/os/Getpagesize.lean`; the Linux file
extension `fsExt`). `runtime`'s `IsPkgInit` instance is Perennial's, whose fact says nothing of
`GOOS`/`GOARCH`, so the
packages that read `GOOS`/`GOARCH` state them in their own facts from these axioms (bbolt's root package,
`bboltRootInit`).
-/
module

public import Perennial.Proof.runtime.Base
public import Perennial.Proof.internal.gomodel.Link
public import Proof.internal.runtime.atomic.Init
public import Proof.internal.runtime.sys.Init
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
namespace runtime
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `runtime`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2», init.«3», init.«4», init.«5», init.«6», init.«7», init.«8»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end runtime
end opaqueInits

namespace runtime

/-- **The trust boundary: the program runs on Linux.** `runtime.GOOS` is the constant
`"linux"` (Go's `GOOS` of the build; goose translates `runtime` names-only, so it is an
axiom `val` with no value). Satisfiable: `GOOS` is an uninterpreted constant. -/
axiom GOOS_linux [GooseExts] [GoGlobalContext] :
    _root_.Perennial.runtime.GOOS = #(go!"linux")

/-- **The trust boundary: the program runs on amd64.** `runtime.GOARCH` is the constant
`"amd64"` (Go's `GOARCH` of the build; an axiom `val` with no value, as `GOOS`). Satisfiable:
`GOARCH` is an uninterpreted constant. -/
axiom GOARCH_amd64 [GooseExts] [GoGlobalContext] :
    _root_.Perennial.runtime.GOARCH = #(go!"amd64")

end runtime

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.runtime.Assumptions]

namespace runtime

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.runtime get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.runtime }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  -- buildVersion: its trusted initializer
  wp_apply _root_.Perennial.runtime.wp_buildVersion_init as Hbv
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.internal.gomodel _root_.Perennial.internal.gomodel.initialize'
      EtcdGrove.ExternalInit.internal_gomodel _root_.Perennial.internal.gomodel.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.internal.runtime.atomic.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.internal.runtime.sys.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  wp_apply (initFuncsOk init.«2» (by mem_tac))
  wp_apply (initFuncsOk init.«3» (by mem_tac))
  wp_apply (initFuncsOk init.«4» (by mem_tac))
  wp_apply (initFuncsOk init.«5» (by mem_tac))
  wp_apply (initFuncsOk init.«6» (by mem_tac))
  wp_apply (initFuncsOk init.«7» (by mem_tac))
  wp_apply (initFuncsOk init.«8» (by mem_tac))
  ipersist Hbv
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.runtime get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.runtime }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end runtime

end init

end Perennial
