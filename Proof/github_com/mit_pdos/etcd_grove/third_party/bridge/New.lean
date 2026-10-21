/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/New.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.New
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.newBridge

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

theorem New.wp_proof (wp_newBridge : newBridge.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro addr l Htb
  wp_start as ⟨#Hrl, Htok⟩
  wp_auto
  wp_apply wp_newBridge addr l Htb $$ [Htok] as %b ⟨%γ, #Hb, Hh, Htok⟩
  · iframe #; iframe
  iapply HΦ
  iframe Htok
  unfold ownBridge
  iexists b, γ
  iframe #
  iframe
  ipureintro; rfl

end proof

end bridgeP
end EtcdGrove
end Perennial
