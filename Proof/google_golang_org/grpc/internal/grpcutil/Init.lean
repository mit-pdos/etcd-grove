/-
Package initialization of `google_golang_org.grpc.internal.grpcutil`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`grpcutilInit`, `cache/v3/Base.lean`): `RegisteredCompressorNames` holds the nil slice
for good. Its initializer allocates it (`var RegisteredCompressorNames []string`, `compressor.go`, no
initializer: nil) and initializes its imports. Only `encoding.RegisterCompressor` writes it, which no
translated code calls (compression is outside the grpc model); a program that does gets no proof: it
would need the cell, which `finish` makes persistent.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
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
variable [package_sem : _root_.Perennial.google_golang_org.grpc.internal.grpcutil.Assumptions]

namespace google_golang_org.grpc.internal.grpcutil

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.internal.grpcutil get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.grpcutil }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoSlice) RegisteredCompressorNames _ as HRegisteredCompressorNames
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  ipersist HRegisteredCompressorNames
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.internal.grpcutil get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.grpcutil }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc.internal.grpcutil

end init

end Perennial
