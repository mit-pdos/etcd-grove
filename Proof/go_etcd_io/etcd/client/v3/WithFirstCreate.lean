/-
Proof of `Spec/WithFirstCreate.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithFirstCreate
public import Spec.go_etcd_io.etcd.client.v3.withTop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem WithFirstCreate.wp_proof (wp_withTop : withTop.spec (GF := GF) (hG := hG)) :
    WithFirstCreate.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_withTop (W64 2) (W64 1) as %sl #Hsl
  · iframe #; ipureintro; decide
  iapply HΦ
  iexact Hsl

end proof

end EtcdGrove
end Perennial
