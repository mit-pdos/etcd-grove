/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__toRangeRequest.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__toRangeRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.toRangeRequest.wp_proof : Op.toRangeRequest.spec (GF := GF) (hG := hG) := by
  intro opv o
  wp_start as ⟨#Hat, %Ht, %Hs⟩
  iunfold opFullAt at Hat
  icases Hat with ⟨Hat, #Hkey, %Hf2, -, -⟩
  iunfold opAt at Hat
  icases Hat with ⟨%Hf, #Hend⟩
  unfold OpFields at Hf
  obtain ⟨hc, -, hs, hl, hmin, hmax, hcmin, hcmax, -, -, -, -, hrev, hser, -⟩ := Hf
  obtain ⟨ht, hko, -⟩ := Hf2
  have hs' : opv.sort' = null := Classical.byContradiction fun hne => by
    rw [Hs] at hs; exact absurd (hs.1 hne) (by simp)
  wp_auto
  rw [ht, Ht]
  wp_auto
  rw [hs']
  wp_auto
  iapply HΦ
  iexists _
  iframe
  isplitl []
  · iexact Hkey
  isplitl []
  · iexact Hend
  ipureintro
  simp only [rangeReqOp, rangeWireOf, hl, hrev, hser, hko, hc, hmin, hmax, hcmin, hcmax]
  rfl

end proof

end EtcdGrove
end Perennial
