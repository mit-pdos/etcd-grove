/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.CheckTxnAuth.wp_proof
    (hTxn : apply.checkTxnPermission.spec (GF := GF) (hG := hG)) :
    apply.CheckTxnAuth.spec (GF := GF) (hG := hG) := by
  intro st le γ P f RD on RW ai info dq rt t U
  wp_start as ⟨#Hst, #Hle, Hai, Hrd, Hu, %Hro, #Hrt⟩
  wp_auto
  wp_apply (hTxn st le γ P f RD on RW ai info dq rt t U) $$ [$Hst $Hle $Hai $Hrd $Hu $Hrt] as %err Hai
  · ipureintro; exact Hro
  iapply HΦ; iexact Hai

end proof

end EtcdGrove
end Perennial
