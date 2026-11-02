/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/quietLogger__Infof.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.quietLogger__Infof

@[expose] public section

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

theorem quietLogger.Infof.wp_proof : quietLogger.Infof.spec (GF := GF) (hG := hG) := by
  intro format args
  wp_start
  wp_auto
  wp_end

end proof

end kvreconf
end EtcdGrove
end Perennial
