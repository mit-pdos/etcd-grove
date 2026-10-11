/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Cmp__KeyBytes.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Cmp__KeyBytes
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Compare__GetKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Cmp.KeyBytes.wp_proof (wp_GetKey : Compare.GetKey.spec (GF := GF) (hG := hG)) :
    Cmp.KeyBytes.spec (GF := GF) (hG := hG) := by
  intro cmpp c dq ksl
  wp_start as ⟨Hc, %Hnn, #Hk⟩
  ihave %Hcn := typedPointsto_not_null _ _ _ $$ Hc
  wp_auto
  rw [decide_eq_false Hcn]
  iStructNamed Hc
  wp_auto
  wp_apply wp_GetKey $$ [$Hk]
  · iframe %
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hcn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
