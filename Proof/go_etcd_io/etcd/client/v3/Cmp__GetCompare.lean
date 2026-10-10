/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Cmp__GetCompare.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Cmp__GetCompare
public import Spec.go_etcd_io.etcd.client.v3.Cmp__ensureCompare

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

theorem Cmp.GetCompare.wp_proof (wp_ensureCompare : Cmp.ensureCompare.spec (GF := GF) (hG := hG)) :
    Cmp.GetCompare.spec (GF := GF) (hG := hG) := by
  intro cmpp c
  wp_start as ⟨Hc, %Hnn⟩
  wp_auto
  wp_apply wp_ensureCompare $$ [$Hc] as Hc
  · iframe %
  wp_end

end proof

end EtcdGrove
end Perennial
