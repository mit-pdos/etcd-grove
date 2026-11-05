/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/ready.lean`. Lean-first.

A context with the request timeout (`client.wp_WithTimeout_bg`), a latest `Get` with no read update
(`client_Get_st` at `True`), the cancel.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ready
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

theorem ready.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    ready.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ cl ms V
  wp_start as ⟨#Hcl, #Hregs, #Hst⟩
  rw [show github_com.mit_pdos.etcd_grove.examples.k8s.compactor.compactRevKey = #k8s.compactRevKey
    from rfl]
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny EtcdGrove.rpctypesEtcdError_asTarget _) $$ []
    as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
  (try wp_auto)
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  wp_apply (client.client_Get_st cl ms V ctx cd k8s.compactRevKey slice.nil (fun _ => iprop(True))
      (opSizeOk_opGetModel (K := 15) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide)))
    $$ [] as %resp %err -
  · iframe #
    imodintro
    iapply (BigAndL.bigAndL_intro (P := iprop(True))
      (fun _ _ _ => by iintro -; ileft; ipureintro; rfl))
    itrivial
  (try wp_auto)
  wp_apply Hcancel
  cases err <;> (try wp_auto) <;> iapply HΦ <;> itrivial

end proof

end k8s_compactor
end EtcdGrove
end Perennial
