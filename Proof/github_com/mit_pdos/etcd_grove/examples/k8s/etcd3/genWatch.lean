/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/genWatch.lean` (stage E of 7f-6): a
random seed, then `genWatchFrom`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genWatchFrom

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem genWatch.wp_proof (wp_genWatchFrom : genWatchFrom.spec (GF := GF) (hG := hG)) :
    genWatch.spec (GF := GF) (hG := hG) := by
  intro id c hasC f hf
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
  (try wp_auto)
  wp_apply wp_genWatchFrom n id c hasC f hf as %x %Hx
  (try wp_auto)
  iapply HΦ
  ipureintro; exact Hx

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
