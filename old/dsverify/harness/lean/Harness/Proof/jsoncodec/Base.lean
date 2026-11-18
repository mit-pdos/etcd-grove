/-
The JSON syntax shared by a kit's generated `encoding/json` codec and the lab's json model
(`harness/jsoncodec`, notes/vsr-net.md): its `isPkgInit` (no package-level state) and
`initialize'`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Harness.GeneratedProof.dsverify_lab.harness.jsoncodec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace dsverify_lab.harness.jsoncodec
section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- No package-level state. -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.dsverify_lab.harness.jsoncodec :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.dsverify_lab.harness.jsoncodec :=
  build_get_is_pkg_init_wf

end wps
end dsverify_lab.harness.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : dsverify_lab.harness.jsoncodec.Assumptions]

abbrev dsverify_lab.harness.jsoncodec.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.dsverify_lab.harness.jsoncodec get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val dsverify_lab.harness.jsoncodec.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.jsoncodec }}

omit package_sem in
theorem dsverify_lab.harness.jsoncodec.wp_initialize' :
    dsverify_lab.harness.jsoncodec.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

end spec

end Perennial
