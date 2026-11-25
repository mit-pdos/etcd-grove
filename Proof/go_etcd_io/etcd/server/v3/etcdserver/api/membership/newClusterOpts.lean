/-
Proof of `membership.newClusterOpts.spec` (claim #34, stage 2, 2026-11-25).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.newClusterOpts
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions__applyOpts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.newClusterOpts.wp_proof
    (hApply : membership.ClusterOptions.applyOpts.spec (GF := GF) (hG := hG)) :
    membership.newClusterOpts.spec (GF := GF) (hG := hG) := by
  intro opts f ml
  wp_start as ⟨#Hopts, #Hf⟩
  wp_auto
  irename «$r0» => Hco
  generalize «$r0_ptr» = co at *
  iStructNamed Hco
  wp_apply hApply co opts f ml _ $$ [maxLearners] as Hml
  · iframe #; iframe
  try wp_auto
  iapply HΦ
  iexact Hml

end proof

end EtcdGrove
end Perennial
