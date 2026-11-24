-- The copy for the part `KvNet/` of `RaftNoAx/Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/quietLogger__Debugf.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/quietLogger__Debugf.lean`. Lean-first
(no Rocq counterpart).


-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.quietLogger__Debugf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem quietLogger.Debugf.wp_proof : quietLogger.Debugf.spec (GF := GF) (hG := hG) := by
  intro format args
  wp_start
  wp_auto
  wp_end

end proof

end raft_kvnet
end EtcdGrove
end Perennial
