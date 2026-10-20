/-
Lean-first (no Rocq counterpart).

The proof of `callList`: `WithRange`, `client_List_st`, then the output from the reply (`kvsFrom`, `withKVs`: `listOut`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callList
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.kvsFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.withKVs
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem callList.wp_proof (wp_kvsFrom : kvsFrom.spec (GF := GF) (hG := hG))
    (wp_withKVs : withKVs.spec (GF := GF) (hG := hG))
    (wp_WithRange : EtcdGrove.WithRange.spec (GF := GF) (hG := hG)) :
    callList.spec (GF := GF) (hG := hG) := by
  intro _ cl ep V E γr cid mid hAs Q
  wp_start as ⟨#Hcl, #Hrpc, Hau⟩
  wp_auto
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  imod monoNatLbOwn_0 (GF := GF) γr.committed with #Hc0
  ihave #Hc0' : committedAtLeast (GF := GF) γr (W64 0) $$ []
  · iunfold committedAtLeast
    iExactEq Hc0; rfl
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
  wp_apply (client_List_st cl ep V E γr cid mid context.backgroundCtxVal cd _ [] Q) $$ [Hau]
    as %resp %err Hout
  · iframe #
    iexact Hau
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
    ileft
    ipureintro; rfl

end proof

end linkvtxn
end EtcdGrove
end Perennial
