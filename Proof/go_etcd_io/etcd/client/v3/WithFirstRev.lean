/-
Proof of `Spec/go_etcd_io/etcd/client/v3/WithFirstRev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithFirstRev
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

theorem WithFirstRev.wp_proof (wp_withTop : withTop.spec (GF := GF) (hG := hG)) :
    WithFirstRev.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_withTop (W64 3) (W64 1) as %sl ⟨#Hsl, Hcap⟩
  · iframe #; ipureintro; decide
  iapply HΦ
  iframe Hsl Hcap

end proof

end EtcdGrove
end Perennial
