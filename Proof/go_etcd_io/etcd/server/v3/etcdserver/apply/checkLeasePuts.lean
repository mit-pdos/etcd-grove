/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
theorem apply.checkLeasePuts.wp_proof
    (hKeys : apply.checkLeasePutsKeys.spec (GF := GF) (hG := hG)) :
    apply.checkLeasePuts.spec (GF := GF) (hG := hG) := by
  intro st le γ P f ai info dq id
  wp_start as ⟨#Hst, #Hle, Hai⟩
  ihave #Hle' := Hle
  iunfold apply.isApplyLessor at Hle'
  icases Hle' with ⟨-, %li, %Hli, -, -, -, #HLookup⟩
  subst Hli
  wp_auto
  wp_apply HLookup as %l Hl
  icases Hl with (%Hl | #Hl)
  · subst Hl
    wp_auto
    iapply HΦ; iframe Hai; iapply applyErrIs_nil
  · ihave #Hl' := Hl
    iunfold apply.leaseIs at Hl'
    icases Hl' with ⟨%Hln, -⟩
    simp only [Hln, decide_false, Bool.not_false]
    wp_auto
    wp_apply (hKeys st P f ai info dq l id) $$ [$Hst $Hai $Hl] as %err ⟨Hai, #HeI⟩
    iapply HΦ; iframe Hai HeI

end proof

end EtcdGrove
end Perennial
