/-
Package initialization of `google_golang_org.grpc.peer`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.grpc.credentials.Init
public import Proof.net.Init

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
variable [package_sem : _root_.Perennial.google_golang_org.grpc.peer.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace google_golang_org.grpc.peer

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.peer get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.peer }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply _root_.Perennial.google_golang_org.grpc.credentials.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.net.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish


end google_golang_org.grpc.peer

end init

end Perennial
