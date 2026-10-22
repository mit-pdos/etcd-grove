/-
Lean-first (no Rocq counterpart).

The proof of `callPut`: `client.client_Put_st`, then the output from the reply's header revision.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callPut
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

theorem callPut.wp_proof : callPut.spec (GF := GF) (hG := hG) := by
  intro _ cl ms V hAs key val Q
  wp_start as ⟨#Hcl, #Hone, #Hregs, Hau⟩
  wp_auto
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  ihave #Hnil := optsAt_nil (GF := GF)
  (try wp_auto)
  ihave #Hrr := client.kvRegs_put ms $$ Hregs
  ihave #Hst' := client.srvStart_idx ms $$ Hst
  wp_apply (client.client_Put_st cl ms V context.backgroundCtxVal cd key val slice.nil Q) $$ [Hau]
    as %resp %err Hout
  · iframe #
    iexact Hau
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hrev, hb⟩ := Hσ
    iunfold putRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %pk, #Hh, #Hhf, -⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    iapply HΦ
    iright
    iexists σ
    iframe HQ
    ipureintro
    refine ⟨?_, hb⟩
    rw [← hrev]
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
