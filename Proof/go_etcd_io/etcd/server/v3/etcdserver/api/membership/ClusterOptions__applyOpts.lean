/-
Proof of `membership.ClusterOptions.applyOpts.spec` (claim #34, stage 2, 2026-11-25): the range over
the one option, which stores its `maxLearners`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions__applyOpts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

attribute [-instance] pure_wp_slice_for_range

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.ClusterOptions.applyOpts.wp_proof :
    membership.ClusterOptions.applyOpts.spec (GF := GF) (hG := hG) := by
  intro co opts f ml ml0
  wp_start as ⟨#Hopts, #Hf, Hml⟩
  wp_auto
  wp_func_lits
  wp_apply (membership.wp_slice_for_range_ro (V := GoFunc) _ opts [f] DFrac.discard _
    (fun i => iprop(opt_ptr ↦ (if i = 0 then (zero_val GoFunc : GoFunc) else f) ∗
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions go!"maxLearners" co ↦ (if i = 0 then ml0 else ml))))
    $$ Hopts [opt Hml]
  · simp only [↓reduceIte]; iframe
  · imodintro
    iintro %i %x %hx ⟨Hopt, Hml⟩ Hopts
    have hi : i = 0 := by
      have := (List.getElem?_eq_some_iff.1 hx).1; simp at this; omega
    subst hi
    have hxf : x = f := by simpa using hx
    subst hxf
    simp only [↓reduceIte]
    wp_auto
    iunfold membership.clusterOptMax at Hf
    wp_apply Hf $$ Hml as Hml
    wp_auto
    iframe
    simp only [Nat.zero_add, one_ne_zero, ↓reduceIte]
    iframe
  iintro ⟨Hopt, Hml⟩ Hopts
  simp only [List.length_singleton, one_ne_zero, ↓reduceIte]
  wp_auto
  iapply HΦ
  iexact Hml

end proof

end EtcdGrove
end Perennial
