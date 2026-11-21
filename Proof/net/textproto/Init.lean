/-
Package initialization of `net.textproto`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`textprotoInit`, `Proof/net/textproto/Base.lean`; prove-http3, 2026-11-21):
`commonHeaderOnce` is the `sync.Once` of `initCommonHeader`, whose action owns the variable
`commonHeader`. Its initializer allocates its variables, initializes its imports and runs their
translated initializers: `errMessageTooLarge = errors.New(...)` (Perennial's `errors.wp_New`) and the
byte slices `colon`, `nl`, `crnl`, `dotcrnl`; the zero `commonHeaderOnce` and the variable
`commonHeader` then make the `Once` (Perennial's `sync.init_Once`).
-/
module

public import Proof.net.textproto.Base
public import Perennial.Proof.errors.Link
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
variable [package_sem : _root_.Perennial.net.textproto.Assumptions]

namespace net.textproto

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.textproto get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.textproto }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoSlice) dotcrnl _ as Hdotcrnl
  wp_apply wp_GlobalAlloc (V := GoSlice) crnl _ as Hcrnl
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Once) commonHeaderOnce _ as HcommonHeaderOnce
  wp_apply wp_GlobalAlloc (V := Loc) commonHeader _ as HcommonHeader
  wp_apply wp_GlobalAlloc (V := GoSlice) nl _ as Hnl
  wp_apply wp_GlobalAlloc (V := GoSlice) colon _ as Hcolon
  wp_apply wp_GlobalAlloc (V := GoInterface) errMessageTooLarge _ as HerrMessageTooLarge
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of errMessageTooLarge))
  -- translated initializer of colon))
  -- translated initializer of nl))
  -- translated initializer of crnl))
  -- translated initializer of dotcrnl))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New as %xE -
  try wp_auto
  wp_apply wp_string_to_bytes _ as %scolon ⟨Scolon, -⟩
  try wp_auto
  try wp_auto
  wp_apply wp_string_to_bytes _ as %snl ⟨Snl, -⟩
  try wp_auto
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %scrnl ⟨Scrnl, -⟩
  try wp_auto
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sdotcrnl ⟨Sdotcrnl, -⟩
  try wp_auto
  ihave HP : (net.textproto.commonHeaderVar : IProp GF) $$ [HcommonHeader]
  · unfold net.textproto.commonHeaderVar; iexists _; iexact HcommonHeader
  imod (_root_.Perennial.sync.init_Once _ _ net.textproto.commonHeaderOk ⊤) $$ [HcommonHeaderOnce HP] with #HOnce
  · iframe
  try wp_auto
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold net.textproto.textprotoInit net.textproto.textprotoInitLC
  iexact HOnce

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.textproto get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.textproto }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end net.textproto

end init

end Perennial
