/-
Package initialization of `net.url`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`urlInit`, `url/PkgInit.lean`): `table` holds `encTableList`, the entries
`gen_encoding_table.go` computes, read-only for good. Its initializer allocates `table`, initializes
`strings` and stores the table's literal (phase 7 S5, 2026-11-24: translated, with `shouldEscape`,
`unescape`, `escape`, `EscapedPath`).
-/
module

public import Proof.net.url.PkgInit
public import Perennial.Proof.strings.Link
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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.url.Assumptions]

namespace net.url

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.url get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.url }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) table _ as Htable
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of table))
  try wp_auto
  ipersist Htable
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  unfold urlInit
  iexists _; iframe Htable
  ipureintro
  set_option maxRecDepth 100000 in decide

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.url get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.url }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end net.url

end init

end Perennial
