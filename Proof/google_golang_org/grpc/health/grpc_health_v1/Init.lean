/-
Package initialization of `google_golang_org.grpc.health.grpc_health_v1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.BaseGrpc
public import Perennial.Proof.context.Link
public import Proof.google_golang_org.grpc.Init

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

section opaqueInits
namespace google_golang_org.grpc.health.grpc_health_v1
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.grpc.health.grpc_health_v1`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([HealthCheckResponse_ServingStatus_name.init,
        HealthCheckResponse_ServingStatus_value.init,
        file_grpc_health_v1_health_proto_enumTypes.init,
        file_grpc_health_v1_health_proto_msgTypes.init,
        file_grpc_health_v1_health_proto_goTypes.init,
        file_grpc_health_v1_health_proto_depIdxs.init,
        Health_ServiceDesc.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end google_golang_org.grpc.health.grpc_health_v1
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.grpc.health.grpc_health_v1.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace google_golang_org.grpc.health.grpc_health_v1

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.health.grpc_health_v1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply _root_.Perennial.google_golang_org.grpc.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.context.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk HealthCheckResponse_ServingStatus_name.init (by mem_tac))
  wp_apply (opaqueInitsOk HealthCheckResponse_ServingStatus_value.init (by mem_tac))
  wp_apply (opaqueInitsOk file_grpc_health_v1_health_proto_enumTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_grpc_health_v1_health_proto_msgTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_grpc_health_v1_health_proto_goTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_grpc_health_v1_health_proto_depIdxs.init (by mem_tac))
  wp_apply (opaqueInitsOk Health_ServiceDesc.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish


end google_golang_org.grpc.health.grpc_health_v1

end init

end Perennial
