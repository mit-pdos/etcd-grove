/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__ResultChan.lean` (k8s 7f-5b). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__ResultChan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem watchChan.ResultChan.wp_proof : watchChan.ResultChan.spec (GF := GF) (hG := hG) := by
  intro wc ch
  wp_start as #Hch
  wp_auto
  iapply HΦ
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
