/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/holdForever.lean` (putgetk's).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.holdForever
public import Perennial.Spec.time.Sleep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

theorem holdForever.wp_proof (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    holdForever.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_for
  wp_apply wp_Sleep
  wp_for_post
  iframe

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial

end
