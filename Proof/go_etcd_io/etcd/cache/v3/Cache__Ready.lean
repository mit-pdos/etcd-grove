/-
Proof of `Spec/Cache__Ready.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__Ready
public import Spec.go_etcd_io.etcd.cache.v3.ready__Ready

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.Ready.wp_proof
    (wp_Ready : ready.Ready.spec (GF := GF) (hG := hG)) :
    Cache.Ready.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap e0
  wp_start as ⟨Hc, #Hlb⟩
  iNamed Hc
  wp_auto
  wp_apply wp_Ready $$ [$HisReady $Hlb] as %b Hb
  iapply HΦ $$ Hb

end proof

end EtcdGrove
end Perennial
