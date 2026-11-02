/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/quietLogger__Errorf.lean`. Lean-first
(no Rocq counterpart).


-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.quietLogger__Errorf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

theorem quietLogger.Errorf.wp_proof : quietLogger.Errorf.spec (GF := GF) (hG := hG) := by
  intro format args
  wp_start
  wp_auto
  wp_end

end proof

end kvdurable
end EtcdGrove
end Perennial
