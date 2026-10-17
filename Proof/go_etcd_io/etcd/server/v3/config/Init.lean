/-
Package initialization of `go_etcd_io.etcd.server.v3.config`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.transport.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery.Init
public import Proof.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.Init
public import Proof.go_uber_org.zap.Init

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.config.Assumptions]

namespace go_etcd_io.etcd.server.v3.config

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.config get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.types.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.transport.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.go_etcd_io.bbolt.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.go_uber_org.zap.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.time.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish


end go_etcd_io.etcd.server.v3.config

end init

end Perennial
