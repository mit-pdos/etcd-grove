module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.reliableLo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem reliableLo.wp_proof : reliableLo.spec (GF := GF) (hG := hG) := by
  intro x req lo Hreq
  have hmax : (#(functions go.max [go.uint64, go.uint64]) : val) = max.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.max) (type_args := List.replicate 2 go.uint64)
  wp_start as -
  wp_auto
  iterate 4
    all_goals (try simp only [hmax])
    all_goals (try wp_auto)
    all_goals (try wp_if_destruct)
  all_goals
    iapply HΦ
    ipureintro
    unfold reliableLoL
    first | (simp_all; done) | (simp_all; word) | word

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
