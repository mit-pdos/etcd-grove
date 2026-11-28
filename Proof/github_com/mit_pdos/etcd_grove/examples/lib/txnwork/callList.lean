/-
Lean-first (no Rocq counterpart).

The proof of `callList`: `WithRange`, `client_List_st`, then the output from the reply (`kvsFrom`, `withKVs`: `listOut`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.callList
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.kvsFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.withKVs
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Perennial.Proof.context.Link
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.CallsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.lib.txnwork go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Assumptions]

theorem callList.wp_proof (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_kvsFrom : kvsFrom.spec (GF := GF) (hG := hG))
    (wp_withKVs : withKVs.spec (GF := GF) (hG := hG))
    (wp_WithRange : EtcdGrove.WithRange.spec (GF := GF) (hG := hG))
    (h_client_List_st : client_List_st.law (GF := GF) (hG := hG)) :
    callList.spec (GF := GF) (hG := hG) := by
  intro _ cl ms V hAs Q
  wp_start as ⟨Hlt, #Hcl, #Hregs, #Hau⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  (try wp_auto)
  wp_apply wp_WithRange listTo as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts : optsAt (GF := GF) _ [withRangeM listTo] $$ []
  · unfold optsAt
    iexists [f]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg; subst Hf' Hg; iexact Hf
    · simp at Hf'
  (try wp_auto)
  wp_apply (h_client_List_st cl ms V cctx ccd _ Q
      (opSizeOk_opGetModel (K := inMax) (E := inMax) (V := 0)
        (optsKeep_cons (withRangeM_keep (by decide)) (optsKeep_nil _ _ _)) (by decide) (by decide))) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
  -- `cancel()`
  (try wp_auto)
  wp_apply Hccancel
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hkvs, hrev, hb⟩ := Hσ
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    wp_apply wp_kvsFrom sl ps m.kvs as %ko ⟨Hko, -⟩
    · iframe #
    (try wp_auto)
    wp_apply wp_withKVs _ ko _ (DFrac.own 1) $$ [Hko] as %o' ⟨-, %Ho'⟩
    · iframe
    iapply HΦ
    iframe Hlt
    iright
    iexists σ
    iframe HQ
    ipureintro
    refine ⟨?_, hb⟩
    rw [Ho', ← hkvs, hrev]
    rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; rfl

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
