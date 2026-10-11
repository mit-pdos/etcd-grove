/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/realTimer__Chan.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.realTimer__Chan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem realTimer.Chan.wp_proof : realTimer.Chan.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as #Hr
  unfold isRealTimer
  icases Hr with ⟨%t, %ch, %γ, #Ht, #HT⟩
  unfold time.isTimer
  icases HT with ⟨#HC, #Hbag⟩
  wp_auto
  iapply HΦ
  iexact Hbag

end proof

end EtcdGrove
end Perennial
