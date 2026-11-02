/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__fileOf.lean`. Lean-first
(no Rocq counterpart).

The cluster's `dir` (read-only in `isClusterC`), `"/replica-"`, and `itoa(id)`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__fileOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.itoa
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.fileOf.wp_proof (wp_itoa : itoa.spec (GF := GF) (hG := hG)) :
    Cluster.fileOf.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c id
  wp_start as Hc
  iunfold isClusterC at Hc
  iNamed Hc
  wp_auto
  wp_apply wp_itoa id $$ [$Hpkg]
  unfold kdFileName
  iapply HΦ
  itrivial

end proof

end kvdurable
end EtcdGrove
end Perennial
