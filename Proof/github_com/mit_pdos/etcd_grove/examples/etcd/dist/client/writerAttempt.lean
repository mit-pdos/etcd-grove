/- Proof of `Spec/.../dist/client/writerAttempt.lean` (#50 N10a): arithmetic only. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerAttempt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

theorem writerAttempt.wp_proof : writerAttempt.spec (GF := GF) (hG := hG) := by
  intro nops
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
