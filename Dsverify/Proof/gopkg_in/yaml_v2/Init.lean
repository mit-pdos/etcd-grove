/-
Package initialization of `gopkg_in.yaml_v2`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the trusted
initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).
-/
module

public import Dsverify.Proof.gopkg_in.yaml_v2.Base
public import Net.Proof.runtime.PkgInitExt

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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.gopkg_in.yaml_v2.Assumptions]

namespace gopkg_in.yaml_v2

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.gopkg_in.yaml_v2 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.gopkg_in.yaml_v2 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_call  -- disableLineWrapping: its trusted initializer does nothing
  wp_call  -- mapItemType: its trusted initializer does nothing
  wp_call  -- durationType: its trusted initializer does nothing
  wp_call  -- defaultMapType: its trusted initializer does nothing
  wp_call  -- ifaceType: its trusted initializer does nothing
  wp_call  -- timeType: its trusted initializer does nothing
  wp_call  -- ptrTimeType: its trusted initializer does nothing
  wp_call  -- base60float: its trusted initializer does nothing
  wp_call  -- default_tag_directives: its trusted initializer does nothing
  wp_call  -- resolveTable: its trusted initializer does nothing
  wp_call  -- resolveMap: its trusted initializer does nothing
  wp_call  -- yamlStyleFloat: its trusted initializer does nothing
  wp_call  -- allowedTimestampFormats: its trusted initializer does nothing
  wp_call  -- structMap: its trusted initializer does nothing
  wp_call  -- eventStrings: its trusted initializer does nothing
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.gopkg_in.yaml_v2 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.gopkg_in.yaml_v2 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end gopkg_in.yaml_v2

end init

end Perennial
