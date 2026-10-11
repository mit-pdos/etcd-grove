/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/WithTTL.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithTTL
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem WithTTL.wp_proof (hZI : zap.Int64.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG)) : WithTTL.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as #Hpkg
  iapply wp_fupd
  wp_auto
  ipersist ttl
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold sessionOptSpec
  imodintro
  iintro %p %o %lg
  wp_start as ⟨Hp, %Hlg⟩
  wp_auto
  have hz : sint.Z (W64 0) = 0 := by decide
  rw [hz]
  by_cases h : 0 < sint.Z t
  · rw [decide_eq_true h]
    wp_auto
    iapply HΦ
    simp only [withTTLM, h, ↓reduceIte, SessionOpts.val]
    iexact Hp
  · rw [decide_eq_false h]
    wp_auto
    wp_apply hZI _ _ as %f1 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hW lg _ _ $$ []
    · ipureintro; exact Hlg
    (try wp_auto)
    iapply HΦ
    simp only [withTTLM, h, ↓reduceIte]
    iexact Hp

end proof

end concurrency
end EtcdGrove
end Perennial
