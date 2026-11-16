/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/decodeObj.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.decodeObj

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem decodeObj.wp_proof : decodeObj.spec (GF := GF) (hG := hG) := by
  intro Obj S W codec vi dsl d o rev hd
  unfold watchContractOk versionerOk
  wp_start as ⟨⟨#Hdec, -⟩, ⟨-, -, #Hupd, -⟩, #Hd⟩
  wp_auto
  wp_apply Hdec $$ [$Hd] as %x %err Hr
  rw [hd]
  icases Hr with ⟨%Herr, %rv, Hx⟩
  subst Herr
  wp_auto
  wp_apply Hupd $$ [$Hx] as %uerr ⟨Hx, %Hue⟩
  subst Hue
  wp_auto
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end k8s
end EtcdGrove
end Perennial
