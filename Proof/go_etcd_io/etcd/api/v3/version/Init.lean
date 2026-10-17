/-
Package initialization of `go_etcd_io.etcd.api.v3.version`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`server/v3/lease/Base.lean`): `Version` and `V3_6` hold fixed values. Its
initializer runs its variables' untranslated initializers (`version.go`): string constants,
`semver` versions (`*semver.New(3, 6, 0, "", "")`), and `AllVersions`; the trust-boundary axioms
`Version_init` and `V3_6_init` state the two the fact reads, `opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base

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
namespace go_etcd_io.etcd.api.v3.version
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.version`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([MinClusterVersion.init,
        APIVersion.init,
        GitSHA.init,
        V3_0.init,
        V3_1.init,
        V3_2.init,
        V3_3.init,
        V3_4.init,
        V3_5.init,
        V3_7.init,
        V3_8.init,
        V3_9.init,
        V4_0.init,
        AllVersions.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `Version = "3.8.0-alpha.0"` (`version.go`): a string. -/
axiom Version_init :
    {{ (True : IProp GF) }} (App (Val Version.init) (Val #()))
    {{ RET #(); ∃ v : GoString, globalAddr Version ↦ v }}

/-- `V3_6 = *semver.New(3, 6, 0, "", "")` (`version.go`): a `semver.Version`. -/
axiom V3_6_init :
    {{ (True : IProp GF) }} (App (Val V3_6.init) (Val #()))
    {{ RET #(); ∃ v : github_com.Masterminds.semver.v3.Version, globalAddr V3_6 ↦ v }}

end go_etcd_io.etcd.api.v3.version
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.version.Assumptions]

namespace go_etcd_io.etcd.api.v3.version

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.version get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (opaqueInitsOk MinClusterVersion.init (by mem_tac))
  wp_apply Version_init as ⟨%vVersion, HVersion⟩
  wp_apply (opaqueInitsOk APIVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk GitSHA.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_0.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_1.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_2.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_3.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_4.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_5.init (by mem_tac))
  wp_apply V3_6_init as ⟨%vV3_6, HV3_6⟩
  wp_apply (opaqueInitsOk V3_7.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_8.init (by mem_tac))
  wp_apply (opaqueInitsOk V3_9.init (by mem_tac))
  wp_apply (opaqueInitsOk V4_0.init (by mem_tac))
  wp_apply (opaqueInitsOk AllVersions.init (by mem_tac))
  ipersist HVersion
  ipersist HV3_6
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish


end go_etcd_io.etcd.api.v3.version

end init

end Perennial
