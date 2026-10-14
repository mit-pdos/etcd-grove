/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/realTimer__Reset.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.realTimer__Reset

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem realTimer.Reset.wp_proof : realTimer.Reset.spec (GF := GF) (hG := hG) := by
  intro r d
  wp_start as #Hr
  unfold isRealTimer
  icases Hr with ⟨%t, %ch, %γ, #Ht, #HT⟩
  wp_auto
  wp_apply time.Timer.wp_Reset t ch γ d $$ [$HT] as %b -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
