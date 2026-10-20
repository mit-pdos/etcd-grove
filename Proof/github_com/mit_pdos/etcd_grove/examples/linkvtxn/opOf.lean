/-
Lean-first (no Rocq counterpart).

The proof of `opOf`: one branch per kind, the client's constructor with no options.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.opOf
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.OpDelete

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem opOf.wp_proof (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG)) :
    opOf.spec (GF := GF) (hG := hG) := by
  intro op m hm
  wp_start as ⟨#Hpkg, #Pc⟩
  ihave #Hnil := optsAt_nil (GF := GF)
  wp_auto
  unfold decTOp at hm
  wp_if_destruct
  · rw [if_pos Hif] at hm
    cases hm
    wp_apply hGet op.Key' slice.nil [] $$ [] as %o #Ho
    · iframe #; ipureintro; exact clientOp_get_ok
    iapply HΦ
    iExactEq Ho; rfl
  · rw [if_neg Hif] at hm
    wp_if_destruct
    · rw [if_pos Hif] at hm
      cases hm
      wp_apply hPut op.Key' op.Val' slice.nil [] $$ [] as %o #Ho
      · iframe #; ipureintro; exact clientOp_put_ok _ _
      iapply HΦ
      iExactEq Ho; rfl
    · rw [if_neg Hif] at hm
      have hk : op.Kind' = W64 2 := by
        by_cases h : op.Kind' = W64 2
        · exact h
        · rw [if_neg h] at hm; cases hm
      rw [if_pos hk] at hm
      cases hm
      wp_apply hDel op.Key' slice.nil [] $$ [] as %o #Ho
      · iframe #; ipureintro; exact clientOp_del_ok _
      iapply HΦ
      iExactEq Ho; rfl

end proof

end linkvtxn
end EtcdGrove
end Perennial
