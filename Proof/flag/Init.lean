/-
Package initialization of `flag`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True` (`Proof/flag/PkgInit.lean`). Its initializer initializes its imports, allocates
its variables, runs their translated initializers (`ErrHelp`, `errParse`, `errRange`: `errors.New`;
`Usage`: a function literal) and its translated `init` function, which reads `os.Args` (`os`'s fact:
some `[]string`, read-only) and sets `CommandLine` to `NewFlagSet(os.Args[0], ExitOnError)`, or
`NewFlagSet("", ExitOnError)` when `os.Args` is empty, then its `Usage` field (featuregate-3,
2026-11-23).
-/
module

public import Proof.flag.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Proof.os.Init
public import Perennial.Proof.errors.NewVar
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
variable [package_sem : _root_.Perennial.flag.Assumptions]

namespace flag

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.flag get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.flag }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _) CommandLine _ as HCommandLine
  wp_apply wp_GlobalAlloc (V := _) Usage _ as HUsage
  wp_apply wp_GlobalAlloc (V := _) errRange _ as HerrRange
  wp_apply wp_GlobalAlloc (V := _) errParse _ as HerrParse
  wp_apply wp_GlobalAlloc (V := _) ErrHelp _ as HErrHelp
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrHelp))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x0 ⟨#_, #E0⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x1 ⟨#_, #E1⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x2 ⟨#_, #E2⟩
  try wp_auto
  -- translated initializer of errParse))
  -- translated initializer of errRange))
  -- translated initializer of Usage))
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  ihave #HA := _root_.Perennial.os.args_of_pkgInit $$ Hd4
  icases HA with ⟨%argsl, %argsxs, #HArgs, #Hargs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hargs
  try wp_auto
  wp_if_destruct
  · try wp_auto
    wp_func_call
    wp_call
    try unfold ExitOnError
    wp_auto
    iframe Hown
    is_pkg_init_finish
  · try wp_auto
    have hpos : 0 < sint.Z argsl.len := by
      have h0 : sint.Z argsl.len ≠ 0 := fun h => Hif (by word)
      omega
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z argsl.len := ⟨by decide, by word⟩
    have hxl : 0 < argsxs.length := by word
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index argsl (sint.Z (W64 0)) argsxs DFrac.discard (argsxs[0]'hxl)
      hb.1 $$ [Hargs] as -
    · iframe #; ipureintro; simp [List.getElem?_eq_getElem hxl]
    wp_func_call
    wp_call
    try unfold ExitOnError
    wp_auto
    iframe Hown
    is_pkg_init_finish
  -- translated initializer of _root_.Perennial.os.Args))
  -- translated initializer of CommandLine))

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.flag get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.flag }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end flag

end init

end Perennial
