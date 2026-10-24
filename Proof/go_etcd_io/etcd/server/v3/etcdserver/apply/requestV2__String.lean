/-
Proof of `(*requestV2).String` (`legacy_request.go:92`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2__String

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply
  go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.requestV2.String.wp_proof :
    apply.requestV2.String.spec (GF := GF) (hG := hG) := by
  intro r_ptr r dq
  wp_start as Hr
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  icases (typedPointsto_not_null_dup _ _ _) $$ Hr with ⟨Hr, %Hrn⟩
  iStructNamed Hr
  wp_auto
  wp_apply (wp_slice_literal (l := [interface.mkOk go.uint64 #r.ID',
    interface.mkOk go.string #r.Method', interface.mkOk go.string #r.Path']))
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Pfmt $Hasl] as %s ⟨-, %Hout⟩
  case wf =>
    refine _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _)
      (_root_.Perennial.fmt.ArgsWf.cons_string _ _
        (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))
  iapply HΦ
  isplitl [ID Method Path Val]
  · iapply typedPointsto_combine r_ptr _ dq Hrn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro
  exact Hout

end proof

end EtcdGrove
end Perennial
