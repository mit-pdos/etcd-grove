/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__acceptAll.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__acceptAll

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

theorem watchChan.acceptAll.wp_proof : watchChan.acceptAll.spec (GF := GF) (hG := hG) := by
  intro Obj S wc p sel emp
  unfold selPredOkW
  wp_start as ⟨#Hp, ⟨-, -, #Hempty⟩⟩
  wp_auto
  wp_apply Hempty $$ [$Hp] as #Hp
  iapply HΦ; itrivial

end proof

end k8s
end EtcdGrove
end Perennial
