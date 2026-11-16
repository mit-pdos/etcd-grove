/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__watchContext.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__watchContext

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

theorem store.watchContext.wp_proof : store.watchContext.spec (GF := GF) (hG := hG) := by
  intro sp ctx P Ψ hW Φ
  iintro ⟨#Hpkg, HP⟩ HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_bind (App (Val _) (Val _))
  iapply hW $$ HP
  inext
  iintro %c Hc
  wp_auto
  iapply HΦ $$ Hc

end proof

end k8s
end EtcdGrove
end Perennial
