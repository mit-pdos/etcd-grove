/-
Package initialization of `sigs_k8s_io.structured_merge_diff.v7.fieldpath`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True` (`Base.lean`). Its initializer allocates its translated variables,
initializes its imports, sets them (`AssociativeListCandidateFieldNames`, a `[]string` literal;
`ErrUnknownPathElementType`, an `errors.New` error, Perennial's `errors.wp_New_errorString`; the
`pe*SepBytes`, `[]byte` literals) and runs the trusted initializers of the others
(`TrustedCode/sigs_k8s_io/structured_merge_diff/v7/fieldpath.lean`: models that do nothing).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.iter.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Init
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
variable [package_sem : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace sigs_k8s_io.structured_merge_diff.v7.fieldpath

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) peKeySepBytes _ as HpeKeySepBytes
  wp_apply wp_GlobalAlloc (V := _) peIndexSepBytes _ as HpeIndexSepBytes
  wp_apply wp_GlobalAlloc (V := _) peValueSepBytes _ as HpeValueSepBytes
  wp_apply wp_GlobalAlloc (V := _) peFieldSepBytes _ as HpeFieldSepBytes
  wp_apply wp_GlobalAlloc (V := _) ErrUnknownPathElementType _ as HErrUnknownPathElementType
  wp_apply wp_GlobalAlloc (V := _) AssociativeListCandidateFieldNames _ as HAssociativeListCandidateFieldNames
  wp_apply (_root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.slices _root_.Perennial.slices.initialize'
      EtcdGrove.ExternalInit.slices _root_.Perennial.slices.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.iter _root_.Perennial.iter.initialize'
      EtcdGrove.ExternalInit.iter _root_.Perennial.iter.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of AssociativeListCandidateFieldNames))
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  try wp_auto
  -- translated initializer of ErrUnknownPathElementType))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
  try wp_auto
  wp_call  -- allowInvalidUTF8: its trusted initializer does nothing
  wp_call  -- allowDuplicates: its trusted initializer does nothing
  -- translated initializer of peFieldSepBytes))
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  try wp_auto
  -- translated initializer of peValueSepBytes))
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  try wp_auto
  -- translated initializer of peIndexSepBytes))
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  try wp_auto
  -- translated initializer of peKeySepBytes))
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  try wp_auto
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- pool: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end sigs_k8s_io.structured_merge_diff.v7.fieldpath

end init

end Perennial
