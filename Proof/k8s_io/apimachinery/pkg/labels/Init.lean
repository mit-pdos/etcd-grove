/-
Package initialization of `k8s_io.apimachinery.pkg.labels`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`labelsInit`, `storage/etcd3/Base.lean`; #25, 2026-11-21): its shared selectors,
read-only for good, `sharedEverythingSelector` an empty `internalSelector` and `sharedNothingSelector`
a `nothingSelector` (`Everything`, `MatchesNothing`). Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): the operator slices `unaryOperators`, `binaryOperators` (literals) and
`validRequirementOperators` (their `append`), the shared selectors `sharedEverythingSelector` (an
empty `internalSelector` literal) and `sharedNothingSelector` (an empty struct literal), the map
literal `string2token` and `var _ Selector = ValidatedSetSelector{}` (an empty map literal).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.apimachinery.pkg.selection.Init
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
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.labels.Assumptions]

namespace k8s_io.apimachinery.pkg.labels

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.labels get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _) string2token _ as Hstring2token
  wp_apply wp_GlobalAlloc (V := _) sharedNothingSelector _ as HsharedNothingSelector
  wp_apply wp_GlobalAlloc (V := _) sharedEverythingSelector _ as HsharedEverythingSelector
  wp_apply wp_GlobalAlloc (V := _) validRequirementOperators _ as HvalidRequirementOperators
  wp_apply wp_GlobalAlloc (V := _) binaryOperators _ as HbinaryOperators
  wp_apply wp_GlobalAlloc (V := _) unaryOperators _ as HunaryOperators
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.selection.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of unaryOperators))
  try wp_auto
  wp_apply (wp_slice_literal (l := [go!"exists", go!"!"])); isplitr; (· ipureintro; rfl); iintro %su ⟨Su, -⟩
  try wp_auto
  -- translated initializer of binaryOperators))
  try wp_auto
  wp_apply (wp_slice_literal (l := [go!"in", go!"notin", go!"=", go!"==", go!"!=", go!"gt", go!"lt"])); isplitr; (· ipureintro; rfl); iintro %sb ⟨Sb, Cb⟩
  try wp_auto
  -- translated initializer of validRequirementOperators))
  try wp_auto
  wp_apply (wp_slice_append (V := GoString) _ _ _ _ _) $$ [Sb Cb Su] as %sv -
  · iframe Sb Cb Su
  try wp_auto
  -- translated initializer of sharedEverythingSelector))
  try wp_auto
  wp_apply (wp_slice_literal (V := k8s_io.apimachinery.pkg.labels.Requirement) (l := [])); isplitr; (· ipureintro; rfl); iintro %se -
  try wp_auto
  -- translated initializer of sharedNothingSelector))
  -- translated initializer of string2token))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string k8s_io.apimachinery.pkg.labels.Token.ty) as %mHst Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w64) go.string) $$ Hst as Hst
  try wp_auto
  -- translated initializer of unaryOperators))
  -- translated initializer of binaryOperators))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mvs Hvs
  try wp_auto
  ipersist HsharedEverythingSelector
  ipersist HsharedNothingSelector
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold k8s_io.apiserver.pkg.storage.etcd3.labelsInit
  isplitl []
  · iexists se; rw [show (W64 0 : w64) = W64 (go.arrayLiteralSize []) by rfl]; iexact HsharedEverythingSelector
  · iexists _; iexact HsharedNothingSelector

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.labels get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apimachinery.pkg.labels

end init

end Perennial
