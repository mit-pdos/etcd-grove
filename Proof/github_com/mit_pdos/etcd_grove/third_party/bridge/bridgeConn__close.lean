/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridgeConn__close.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridgeConn__close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem bridgeConn.close.wp_proof : bridgeConn.close.spec (GF := GF) (hG := hG) := by
  intro c inc outc donec
  wp_start as ⟨#Hcf, #Hin, #Hout⟩
  iunfold connFields at Hcf
  icases Hcf with ⟨#Hci, #Hco, #Hcd⟩
  wp_auto
  wp_apply net.ConnClose inc $$ [] as %_ -
  · iexact Hin
  wp_apply net.ConnClose outc $$ [] as %_ -
  · iexact Hout
  iapply HΦ
  itrivial

end proof

end bridgeP
end EtcdGrove
end Perennial
