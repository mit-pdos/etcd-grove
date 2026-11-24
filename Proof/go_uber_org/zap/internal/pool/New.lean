/-
Proof of `Spec/go_uber_org/zap/internal/pool/New.lean` over the real code (prove-misc, 2026-11-20).
-/
module

public import Spec.go_uber_org.zap.internal.pool.New

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_uber_org.zap.internal.pool.Assumptions]

theorem zap.internal.pool.New.wp_proof : zap.internal.pool.New.spec (GF := GF) (hG := hG) := by
  intro E fn
  wp_start
  wp_auto
  rw [recv_eq_func_mk BAnon BAnon]
  iapply wp_fupd
  wp_auto
  ipersist fn
  imodintro
  iapply HΦ
  unfold zap.internal.pool.ownPool
  iStructNamed «$r0»
  iexists _
  iframe
  isplitr
  · ipureintro
    exact ⟨rfl, by simp [func.nil]⟩
  imodintro
  iintro %Q #Hfn
  unfold sync.newSpec
  iright
  imodintro
  iintro %Ψ - HΨ
  dsimp only
  wp_auto
  unfold zap.internal.pool.fnSpec
  wp_apply Hfn as %v HQ
  iapply HΨ
  isplitl
  · unfold zap.internal.pool.elemOk
    iexists v
    iframe
    ipureintro
    rfl
  itrivial

end proof

end EtcdGrove
end Perennial
