/-
Proof of `Spec/go_uber_org/zap/internal/pool/Pool__Put.lean` over the real code (zap-z2, 2026-11-23), over
Perennial's linked `sync.Pool.Put` (`sync.Pool.wp_Put`).
-/
module

public import Spec.go_uber_org.zap.internal.pool.Pool__Put
public import Perennial.Proof.sync.Link

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

theorem zap.internal.pool.Pool.Put.wp_proof :
    zap.internal.pool.Pool.Put.spec (GF := GF) (hG := hG) := by
  intro E p Q x
  wp_start as ⟨#Hpool, HQ⟩
  unfold zap.internal.pool.isPool
  icases Hpool with ⟨%f, %hf, #Hsp⟩
  wp_auto
  wp_apply sync.Pool.wp_Put $$ [$Hsp HQ]
  · unfold zap.internal.pool.elemOk
    iexists x
    iframe
    ipureintro
    rfl
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
