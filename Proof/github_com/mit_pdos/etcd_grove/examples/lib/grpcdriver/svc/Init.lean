/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`drvDescs`, `svc/Base.lean`): its service descriptor `Driver_ServiceDesc`, read-only, with
its methods and streams exactly. Its initializer allocates and sets the descriptor (a `grpc.ServiceDesc`
literal) and initializes its imports.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Base
public import Perennial.Proof.context.Link
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.Init
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
variable [package_sem : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Assumptions]

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Driver_ServiceDesc _ as HDriver_ServiceDesc
  wp_apply (_root_.Perennial.google_golang_org.protobuf.types.known.wrapperspb.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of Driver_ServiceDesc))
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pm ⟨Sm, -⟩; wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %ps ⟨Ss, -⟩; wp_auto
  ipersist Sm
  ipersist Ss
  ipersist HDriver_ServiceDesc
  iStructNamed HDriver_ServiceDesc
  iframe Hown
  is_pkg_init_finish
  try imodintro
  unfold github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.drvDescs go_etcd_io.etcd.cache.v3.pbDescIs
  iframe #
  first | (ipureintro; exact ⟨rfl, rfl⟩) | exact ⟨rfl, rfl⟩

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

end init

end Perennial
