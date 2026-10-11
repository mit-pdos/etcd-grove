/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/NewSTMReadCommitted.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewSTMReadCommitted
public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewSTM
public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithAbortContext
public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithIsolation

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem NewSTMReadCommitted.wp_proof (hNew : NewSTM.spec (GF := GF) (hG := hG))
    (hWAC : WithAbortContext.spec (GF := GF) (hG := hG))
    (hWI : WithIsolation.spec (GF := GF) (hG := hG)) :
    NewSTMReadCommitted.spec (GF := GF) (hG := hG) := by
  intro ctx cs c pfx apply Q lo
  wp_start as ⟨#Hctx, #Hcl, #Happ, #Hlo⟩
  wp_auto
  wp_apply hWAC ctx cs $$ [$Hpkg $Hctx] as %f0 #Hf0
  (try wp_auto)
  wp_apply hWI isoRC $$ [$Hpkg] as %f1 #Hf1
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f0, f1])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  (try wp_auto)
  ihave #Hopts : stmOptsAt (GF := GF) _ [id, withIsoM isoRC] $$ []
  · unfold stmOptsAt
    iexists [f0, f1]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf0
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg
      subst Hf Hg; iexact Hf1
    · simp at Hf
  wp_apply hNew c pfx apply Q _ [id, withIsoM isoRC] lo $$ [$Hpkg $Hcl $Happ $Hopts $Hlo]
    as %resp %err #Hres
  · ipureintro
    refine ⟨by simp [stmOptsFold, STMOpts.init, withIsoM, isoValid], ?_⟩
    simp [stmOptsFold, STMOpts.init, withIsoM]
  (try wp_auto)
  iapply HΦ $$ Hres

end proof

end concurrency
end EtcdGrove
end Perennial
