/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/objLabels.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.objLabels

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem objLabels.wp_proof
    : objLabels.spec (GF := GF) (hG := hG) := by
  intro o
  wp_start
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    simp [Hif]
    itrivial
  · wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %m Hm
    (try wp_auto)
    wp_apply (wp_mapInsert go.string m ∅ go!"app" o.App') $$ [$Hm] as Hm
    (try wp_auto)
    iapply HΦ
    simp only [Hif, ite_false, labMapL]
    iexact Hm

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
