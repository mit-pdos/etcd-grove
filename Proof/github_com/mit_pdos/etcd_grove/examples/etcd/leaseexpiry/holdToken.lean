/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiry/holdToken.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.holdToken
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiry

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Assumptions]

theorem holdToken.wp_proof : holdToken.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave IH : iprop(True) $$ []
  · itrivial
  wp_for IH
  wp_apply time.wp_Sleep
  wp_for_post
  iframe

end proof

end etcd_leaseexpiry
end EtcdGrove
end Perennial
