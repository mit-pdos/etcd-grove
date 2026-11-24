/-
Proof of `Spec/go_uber_org/zap/internal/pool/Pool__Get.lean` over the real code (zap-z2, 2026-11-23), over
Perennial's linked `sync.Pool.Get` (`sync.Pool.wp_Get`).
-/
module

public import Spec.go_uber_org.zap.internal.pool.Pool__Get
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

theorem zap.internal.pool.Pool.Get.wp_proof :
    zap.internal.pool.Pool.Get.spec (GF := GF) (hG := hG) := by
  intro E p Q
  wp_start as #Hpool
  unfold zap.internal.pool.isPool
  icases Hpool with ⟨%f, %hf, #Hsp⟩
  wp_auto
  wp_apply sync.Pool.wp_Get $$ [$Hsp] as %x ⟨(Hx | %Hnil), -⟩
  · unfold zap.internal.pool.elemOk
    icases Hx with ⟨%v, %hx, HQ⟩
    subst hx
    wp_auto
    iapply HΦ
    iexact HQ
  · exact absurd Hnil.1 hf

end proof

end EtcdGrove
end Perennial
