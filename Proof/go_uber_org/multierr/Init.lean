/-
Package initialization of `go_uber_org.multierr`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates its variables, initializes `bytes` and `sync` and runs their
translated initializers (zap-z2, 2026-11-23: zapcore imports it): the separators (`[]byte` of string
constants) and `_bufferPool` (a `sync.Pool` literal whose `New` is a function literal, not called).
-/
module

public import Proof.go_uber_org.zap.PkgInit
public import Perennial.Proof.bytes.Link
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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_uber_org.multierr.Assumptions]

namespace go_uber_org.multierr

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_uber_org.multierr get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.multierr }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Pool) _bufferPool _ as H_bufferPool
  wp_apply wp_GlobalAlloc (V := GoSlice) _multilineIndent _ as H_multilineIndent
  wp_apply wp_GlobalAlloc (V := GoSlice) _multilineSeparator _ as H_multilineSeparator
  wp_apply wp_GlobalAlloc (V := GoSlice) _multilinePrefix _ as H_multilinePrefix
  wp_apply wp_GlobalAlloc (V := GoSlice) _singlelineSeparator _ as H_singlelineSeparator
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of _singlelineSeparator))
  try wp_auto
  wp_apply wp_string_to_bytes _ as %_ ⟨_, -⟩
  try wp_auto
  -- translated initializer of _multilinePrefix))
  try wp_auto
  wp_apply wp_string_to_bytes _ as %_ ⟨_, -⟩
  try wp_auto
  -- translated initializer of _multilineSeparator))
  try wp_auto
  wp_apply wp_string_to_bytes _ as %_ ⟨_, -⟩
  try wp_auto
  -- translated initializer of _multilineIndent))
  try wp_auto
  wp_apply wp_string_to_bytes _ as %_ ⟨_, -⟩
  try wp_auto
  -- translated initializer of _bufferPool))
  try wp_auto
  rw [recv_eq_func_mk BAnon BAnon]
  try wp_auto
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_uber_org.multierr get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.multierr }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_uber_org.multierr

end init

end Perennial
