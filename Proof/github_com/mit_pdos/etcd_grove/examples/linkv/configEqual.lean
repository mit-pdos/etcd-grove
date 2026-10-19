/-
Lean-first (no Rocq counterpart).

The proof of `configEqual`: `entriesEqual` of the stores, then of the pending puts.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.configEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.entriesEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

theorem configEqual.wp_proof (wp_entriesEqual : entriesEqual.spec (GF := GF) (hG := hG)) :
    configEqual.spec (GF := GF) (hG := hG) := by
  intro a b ga gb
  wp_start as ⟨#Ha, #Hb⟩
  unfold cfgOwn
  icases Ha with ⟨#Hak, #Hap⟩
  icases Hb with ⟨#Hbk, #Hbp⟩
  wp_auto
  wp_apply wp_entriesEqual a.kv' b.kv' ga.kv gb.kv DFrac.discard DFrac.discard $$ [$Hak $Hbk] as _
  wp_if_destruct
  · wp_apply wp_entriesEqual a.pend' b.pend' ga.pend gb.pend DFrac.discard DFrac.discard $$ [$Hap $Hbp] as _
    rw [show decide (ga.pend = gb.pend) = decide (ga = gb) by
      cases ga; cases gb; simp only at Hif ⊢; subst Hif; simp]
    iapply HΦ; itrivial
  · rw [show decide (ga = gb) = false from decide_eq_false (fun h => Hif (by rw [h]))]
    iapply HΦ; itrivial

end proof

end linkv
end EtcdGrove
end Perennial
