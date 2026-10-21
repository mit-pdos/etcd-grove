/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/dialer__Dial.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.dialer__Dial
public import Spec.net.Dial

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem dialer.Dial.wp_proof (wp_Dial : net.Dial.spec (GF := GF) (hG := hG)) :
    dialer.Dial.spec (GF := GF) (hG := hG) := by
  intro addr
  wp_start as -
  wp_auto
  wp_apply wp_Dial go!"tcp" addr $$ [] as %c %err Hr
  · ipureintro; rfl
  iapply HΦ
  iexact Hr

end proof

end bridge
end EtcdGrove
end Perennial
