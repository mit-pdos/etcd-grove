/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__tick.lean`. Lean-first
(no Rocq counterpart).

`(1 + below(4)) * time.Millisecond`: between 1 and 4 ms, positive.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__tick
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.tick.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    Cluster.tick.spec (GF := GF) (hG := hG) := by
  intro γr vs c
  wp_start as Hc
  iunfold isClusterC at Hc
  iNamed Hc
  wp_auto
  wp_apply wp_below (W64 4) $$ [$Hpkg] as %r %Hr
  iapply HΦ
  ipureintro
  have h := Hr.2 (by decide)
  have hr : r = W64 0 ∨ r = W64 1 ∨ r = W64 2 ∨ r = W64 3 := by word
  rcases hr with rfl | rfl | rfl | rfl <;> decide

end proof

end kvreconf
end EtcdGrove
end Perennial
